// Terminal Space Invaders - multiplayer over TCP (Go standard library only).
//
// Run it, then choose:
//   1) Host a game  - wait in the lobby for players, press ENTER to start
//   2) Join a game  - enter the host's address (host:port) and your name
//
// The host is authoritative: it runs the game simulation and broadcasts a
// snapshot to every client ~20 times per second. Clients only send key presses.
//
// Works on macOS / Linux / WSL (uses `stty` for raw keyboard input).
// Needs a terminal of at least 80x24.
package main
 
import (
	"bufio"
	"encoding/json"
	"fmt"
	"math/rand"
	"net"
	"os"
	"os/exec"
	"os/signal"
	"sort"
	"strings"
	"sync"
	"syscall"
	"time"
	"unicode"
)
 
const (
	W, H         = 50, 20 // playfield size (cells)
	tickDur      = 50 * time.Millisecond
	invRows      = 5
	invCols      = 8
	invDX, invDY = 4, 2 // spacing between invaders
	maxPlayers   = 6
	maxNameLen   = 12
	defaultPort  = "9000"
)
 
// ---------------------------------------------------------------------------
// Network protocol (newline-delimited JSON)
// ---------------------------------------------------------------------------
 
// ClientMsg is sent from client to host.
type ClientMsg struct {
	Type string `json:"type"` // "hello" | "input"
	Name string `json:"name,omitempty"`
	Key  string `json:"key,omitempty"` // "left" | "right" | "fire"
}
 
type PlayerView struct {
	ID    int    `json:"id"`
	Name  string `json:"name"`
	X     int    `json:"x"`
	Score int    `json:"score"`
	Lives int    `json:"lives"`
	Alive bool   `json:"alive"`
	Blink bool   `json:"blink"`
}
 
// Snapshot is sent from host to clients every tick.
type Snapshot struct {
	Phase    string       `json:"phase"` // lobby | playing | over | rejected
	You      int          `json:"you"`
	Level    int          `json:"level"`
	Msg      string       `json:"msg"`
	Players  []PlayerView `json:"players"`
	Invaders [][3]int     `json:"invaders"` // x, y, row
	Bullets  [][2]int     `json:"bullets"`
	Bombs    [][2]int     `json:"bombs"`
}
 
// ---------------------------------------------------------------------------
// Game simulation (runs on the host only)
// ---------------------------------------------------------------------------
 
type clientConn struct {
	conn net.Conn
	out  chan []byte
	done chan struct{}
}
 
type player struct {
	id, x, score, lives int
	name                string
	alive               bool
	invuln, cooldown    int
	cc                  *clientConn // nil for the host's own player
}
 
type bullet struct{ x, y, owner int }
 
type invStats struct{ alive, minC, maxC, maxR int }
 
type game struct {
	mu      sync.Mutex
	phase   string
	level   int
	tick    int
	nextID  int
	players map[int]*player
 
	inv         [invRows][invCols]bool
	ox, oy, dir int
	bullets     []bullet
	bombs       []bullet
 
	msg      string
	msgTicks int
}
 
func newGame() *game {
	return &game{phase: "lobby", level: 1, nextID: 1, players: map[int]*player{}}
}
 
func abs(a int) int {
	if a < 0 {
		return -a
	}
	return a
}
 
// sortedIDs must be called with g.mu held.
func (g *game) sortedIDs() []int {
	ids := make([]int, 0, len(g.players))
	for id := range g.players {
		ids = append(ids, id)
	}
	sort.Ints(ids)
	return ids
}
 
func (g *game) tryAddPlayer(name string, cc *clientConn) (*player, string) {
	g.mu.Lock()
	defer g.mu.Unlock()
	if g.phase != "lobby" {
		return nil, "The game has already started."
	}
	if len(g.players) >= maxPlayers {
		return nil, "The game is full."
	}
	p := &player{id: g.nextID, name: name, lives: 3, alive: true, cc: cc}
	g.nextID++
	g.players[p.id] = p
	return p, ""
}
 
func (g *game) removePlayer(id int) {
	g.mu.Lock()
	defer g.mu.Unlock()
	delete(g.players, id)
}
 
func (g *game) closeAll() {
	g.mu.Lock()
	defer g.mu.Unlock()
	for _, p := range g.players {
		if p.cc != nil {
			p.cc.conn.Close()
		}
	}
}
 
// startLevel must be called with g.mu held.
func (g *game) startLevel() {
	for r := range g.inv {
		for c := range g.inv[r] {
			g.inv[r][c] = true
		}
	}
	g.ox, g.oy, g.dir = 2, 1, 1
	g.bullets, g.bombs = nil, nil
	g.tick = 0
}
 
// startGame must be called with g.mu held.
func (g *game) startGame() {
	g.level = 1
	ids := g.sortedIDs()
	for i, id := range ids {
		p := g.players[id]
		p.score, p.lives, p.alive, p.invuln, p.cooldown = 0, 3, true, 0, 0
		p.x = (i + 1) * W / (len(ids) + 1)
	}
	g.startLevel()
	g.msg, g.msgTicks = "", 0
	g.phase = "playing"
}
 
// resetToLobby must be called with g.mu held.
func (g *game) resetToLobby() {
	g.phase = "lobby"
	g.msg, g.msgTicks = "", 0
	g.bullets, g.bombs = nil, nil
}
 
func (g *game) finish(msg string) {
	g.phase = "over"
	g.msg = msg
	g.msgTicks = 0
	g.bullets, g.bombs = nil, nil
}
 
func (g *game) handleKey(id int, key string) {
	g.mu.Lock()
	defer g.mu.Unlock()
	p := g.players[id]
	if p == nil || g.phase != "playing" || !p.alive {
		return
	}
	switch key {
	case "left":
		p.x -= 2
		if p.x < 0 {
			p.x = 0
		}
	case "right":
		p.x += 2
		if p.x > W-1 {
			p.x = W - 1
		}
	case "fire":
		if p.cooldown == 0 {
			g.bullets = append(g.bullets, bullet{x: p.x, y: H - 2, owner: id})
			p.cooldown = 6
		}
	}
}
 
func (g *game) alivePlayers() int {
	n := 0
	for _, p := range g.players {
		if p.alive {
			n++
		}
	}
	return n
}
 
func (g *game) stats() invStats {
	s := invStats{minC: invCols, maxC: -1, maxR: -1}
	for r := 0; r < invRows; r++ {
		for c := 0; c < invCols; c++ {
			if !g.inv[r][c] {
				continue
			}
			s.alive++
			if c < s.minC {
				s.minC = c
			}
			if c > s.maxC {
				s.maxC = c
			}
			if r > s.maxR {
				s.maxR = r
			}
		}
	}
	return s
}
 
// Invaders speed up as they die and as the level increases.
func (g *game) moveEvery(alive int) int {
	total := invRows * invCols
	e := 12 - (g.level-1)*2 - 8*(total-alive)/total
	if e < 2 {
		e = 2
	}
	return e
}
 
func (g *game) bombEvery() int {
	e := 16 - 2*g.level
	if e < 4 {
		e = 4
	}
	return e
}
 
func (g *game) dropBombs() {
	n := 1 + (g.alivePlayers()-1)/2
	for ; n > 0; n-- {
		var cols []int
		for c := 0; c < invCols; c++ {
			for r := 0; r < invRows; r++ {
				if g.inv[r][c] {
					cols = append(cols, c)
					break
				}
			}
		}
		if len(cols) == 0 {
			return
		}
		c := cols[rand.Intn(len(cols))]
		for r := invRows - 1; r >= 0; r-- {
			if g.inv[r][c] {
				g.bombs = append(g.bombs, bullet{x: g.ox + c*invDX, y: g.oy + r*invDY + 1})
				break
			}
		}
	}
}
 
func (g *game) collide() {
	// Player bullets vs invaders / bombs.
	keptB := make([]bullet, 0, len(g.bullets))
	for _, b := range g.bullets {
		hit := false
		for r := 0; r < invRows && !hit; r++ {
			for c := 0; c < invCols; c++ {
				if g.inv[r][c] && g.ox+c*invDX == b.x && g.oy+r*invDY == b.y {
					g.inv[r][c] = false
					if p := g.players[b.owner]; p != nil {
						p.score += (invRows - r) * 10
					}
					hit = true
					break
				}
			}
		}
		if !hit {
			for i, bm := range g.bombs {
				if bm.x == b.x && abs(bm.y-b.y) <= 1 {
					g.bombs = append(g.bombs[:i], g.bombs[i+1:]...)
					hit = true
					break
				}
			}
		}
		if !hit {
			keptB = append(keptB, b)
		}
	}
	g.bullets = keptB
 
	// Bombs vs ships.
	keptM := make([]bullet, 0, len(g.bombs))
	for _, bm := range g.bombs {
		hit := false
		if bm.y >= H-1 {
			for _, p := range g.players {
				if p.alive && p.invuln == 0 && p.x == bm.x {
					p.lives--
					if p.lives <= 0 {
						p.alive = false
					} else {
						p.invuln = 40
					}
					hit = true
					break
				}
			}
		}
		if !hit && bm.y < H {
			keptM = append(keptM, bm)
		}
	}
	g.bombs = keptM
}
 
// step advances the simulation by one tick. Call with g.mu held.
func (g *game) step() {
	if g.msgTicks > 0 {
		g.msgTicks--
		if g.msgTicks == 0 && g.phase == "playing" {
			g.msg = ""
		}
	}
	if g.phase != "playing" {
		return
	}
	g.tick++
 
	for _, p := range g.players {
		if p.cooldown > 0 {
			p.cooldown--
		}
		if p.invuln > 0 {
			p.invuln--
		}
	}
 
	if g.tick%2 == 0 { // bullets fly up
		kept := make([]bullet, 0, len(g.bullets))
		for _, b := range g.bullets {
			b.y--
			if b.y >= 0 {
				kept = append(kept, b)
			}
		}
		g.bullets = kept
	}
	if g.tick%4 == 0 { // bombs fall
		for i := range g.bombs {
			g.bombs[i].y++
		}
	}
 
	st := g.stats()
	if st.alive > 0 && g.tick%g.moveEvery(st.alive) == 0 {
		minX, maxX := g.ox+st.minC*invDX, g.ox+st.maxC*invDX
		switch {
		case g.dir > 0 && maxX >= W-1:
			g.oy++
			g.dir = -1
		case g.dir < 0 && minX <= 0:
			g.oy++
			g.dir = 1
		default:
			g.ox += g.dir
		}
	}
	if st.alive > 0 && g.tick%g.bombEvery() == 0 {
		g.dropBombs()
	}
 
	g.collide()
 
	st = g.stats()
	switch {
	case g.alivePlayers() == 0:
		g.finish("GAME OVER - all ships destroyed")
	case st.alive == 0:
		g.level++
		g.startLevel()
		g.msg, g.msgTicks = fmt.Sprintf("Wave %d!", g.level), 40
	case g.oy+st.maxR*invDY >= H-2:
		g.finish("GAME OVER - the invaders landed!")
	}
}
 
// snapshot must be called with g.mu held; it returns an independent copy.
func (g *game) snapshot() Snapshot {
	s := Snapshot{Phase: g.phase, Level: g.level, Msg: g.msg}
	for _, id := range g.sortedIDs() {
		p := g.players[id]
		s.Players = append(s.Players, PlayerView{
			ID: p.id, Name: p.name, X: p.x, Score: p.score, Lives: p.lives,
			Alive: p.alive, Blink: p.invuln > 0 && (g.tick/3)%2 == 0,
		})
	}
	if g.phase == "playing" {
		for r := 0; r < invRows; r++ {
			for c := 0; c < invCols; c++ {
				if g.inv[r][c] {
					s.Invaders = append(s.Invaders, [3]int{g.ox + c*invDX, g.oy + r*invDY, r})
				}
			}
		}
		for _, b := range g.bullets {
			s.Bullets = append(s.Bullets, [2]int{b.x, b.y})
		}
		for _, b := range g.bombs {
			s.Bombs = append(s.Bombs, [2]int{b.x, b.y})
		}
	}
	return s
}
 
// ---------------------------------------------------------------------------
// Host networking
// ---------------------------------------------------------------------------
 
func (g *game) serve(ln net.Listener) {
	for {
		c, err := ln.Accept()
		if err != nil {
			return
		}
		go g.handleConn(c)
	}
}
 
func rejectConn(c net.Conn, msg string) {
	b, _ := json.Marshal(Snapshot{Phase: "rejected", Msg: msg})
	c.SetWriteDeadline(time.Now().Add(2 * time.Second))
	c.Write(append(b, '\n'))
	c.Close()
}
 
func (g *game) handleConn(c net.Conn) {
	dec := json.NewDecoder(c)
	c.SetReadDeadline(time.Now().Add(10 * time.Second))
	var hello ClientMsg
	if err := dec.Decode(&hello); err != nil || hello.Type != "hello" {
		c.Close()
		return
	}
	c.SetReadDeadline(time.Time{})
 
	cc := &clientConn{conn: c, out: make(chan []byte, 8), done: make(chan struct{})}
	p, reason := g.tryAddPlayer(sanitizeName(hello.Name), cc)
	if p == nil {
		rejectConn(c, reason)
		return
	}
	defer func() {
		close(cc.done)
		c.Close()
		g.removePlayer(p.id)
	}()
 
	go func() { // writer
		for {
			select {
			case b := <-cc.out:
				c.SetWriteDeadline(time.Now().Add(2 * time.Second))
				if _, err := c.Write(b); err != nil {
					c.Close()
					return
				}
			case <-cc.done:
				return
			}
		}
	}()
 
	for { // reader
		var m ClientMsg
		if err := dec.Decode(&m); err != nil {
			return
		}
		if m.Type == "input" {
			g.handleKey(p.id, m.Key)
		}
	}
}
 
type target struct {
	id int
	cc *clientConn
}
 
// loop is the host's game loop: step, broadcast, render.
func (g *game) loop(hostID int, hint string, stop <-chan struct{}) {
	ticker := time.NewTicker(tickDur)
	defer ticker.Stop()
	for {
		select {
		case <-stop:
			return
		case <-ticker.C:
		}
 
		g.mu.Lock()
		g.step()
		snap := g.snapshot()
		var targets []target
		for id, p := range g.players {
			if p.cc != nil {
				targets = append(targets, target{id, p.cc})
			}
		}
		g.mu.Unlock()
 
		for _, tg := range targets {
			s := snap
			s.You = tg.id
			b, err := json.Marshal(&s)
			if err != nil {
				continue
			}
			select {
			case tg.cc.out <- append(b, '\n'):
			default: // slow client: drop this frame
			}
		}
 
		snap.You = hostID
		render(&snap, true, hint)
	}
}
 
func runHost(r *bufio.Reader, name, port string) {
	ln, err := net.Listen("tcp", ":"+port)
	if err != nil {
		fmt.Println("Cannot listen on port", port+":", err)
		return
	}
	defer ln.Close()
 
	g := newGame()
	me, _ := g.tryAddPlayer(name, nil)
 
	var addrs []string
	for _, ip := range localIPs() {
		addrs = append(addrs, net.JoinHostPort(ip, port))
	}
	if len(addrs) == 0 {
		addrs = append(addrs, net.JoinHostPort("127.0.0.1", port))
	}
	hint := strings.Join(addrs, "   ")
 
	go g.serve(ln)
 
	restore := setupTerminal()
	defer restore()
 
	stop := make(chan struct{})
	loopDone := make(chan struct{})
	go func() {
		g.loop(me.id, hint, stop)
		close(loopDone)
	}()
 
	keys := make(chan string, 16)
	go readKeys(r, keys)
 
	for k := range keys {
		if k == "quit" {
			break
		}
		if k == "enter" {
			g.mu.Lock()
			switch g.phase {
			case "lobby":
				g.startGame()
			case "over":
				g.resetToLobby()
			}
			g.mu.Unlock()
			continue
		}
		g.handleKey(me.id, k)
	}
	close(stop)
	<-loopDone
	g.closeAll()
}
 
// ---------------------------------------------------------------------------
// Client
// ---------------------------------------------------------------------------
 
func runClient(r *bufio.Reader, addr, name string) {
	conn, err := net.DialTimeout("tcp", addr, 5*time.Second)
	if err != nil {
		fmt.Println("Cannot connect:", err)
		return
	}
	defer conn.Close()
 
	enc := json.NewEncoder(conn)
	if err := enc.Encode(ClientMsg{Type: "hello", Name: name}); err != nil {
		fmt.Println("Cannot send hello:", err)
		return
	}
 
	restore := setupTerminal()
	defer restore()
 
	disc := make(chan string, 1)
	go func() {
		dec := json.NewDecoder(conn)
		for {
			var s Snapshot
			if err := dec.Decode(&s); err != nil {
				disc <- "Disconnected from the host."
				return
			}
			if s.Phase == "rejected" {
				disc <- "Could not join: " + s.Msg
				return
			}
			render(&s, false, "")
		}
	}()
 
	keys := make(chan string, 16)
	go readKeys(r, keys)
 
	for {
		select {
		case msg := <-disc:
			restore()
			fmt.Println(msg)
			return
		case k, ok := <-keys:
			if !ok || k == "quit" {
				return
			}
			if k == "left" || k == "right" || k == "fire" {
				if err := enc.Encode(ClientMsg{Type: "input", Key: k}); err != nil {
					restore()
					fmt.Println("Connection lost.")
					return
				}
			}
		}
	}
}
 
// ---------------------------------------------------------------------------
// Terminal handling & rendering
// ---------------------------------------------------------------------------
 
const reset = "\x1b[0m"
 
var (
	playerColors = []string{"\x1b[92m", "\x1b[96m", "\x1b[93m", "\x1b[95m", "\x1b[94m", "\x1b[97m"}
	invColors    = []string{"\x1b[91m", "\x1b[93m", "\x1b[95m", "\x1b[96m", "\x1b[92m"}
	invChars     = []string{"Y", "M", "W", "H", "O"}
)
 
// setupTerminal puts the terminal in cbreak/no-echo mode (via stty), switches
// to the alternate screen and hides the cursor. The returned func undoes it.
func setupTerminal() func() {
	get := exec.Command("stty", "-g")
	get.Stdin = os.Stdin
	saved, err := get.Output()
	if err != nil {
		fmt.Println("Cannot configure the terminal (is `stty` available? Windows needs WSL).")
		os.Exit(1)
	}
	set := exec.Command("stty", "cbreak", "-echo")
	set.Stdin = os.Stdin
	set.Run()
	fmt.Print("\x1b[?1049h\x1b[?25l\x1b[2J")
 
	var once sync.Once
	restore := func() {
		once.Do(func() {
			fmt.Print("\x1b[?25h\x1b[?1049l")
			rs := exec.Command("stty", strings.TrimSpace(string(saved)))
			rs.Stdin = os.Stdin
			rs.Run()
		})
	}
	sig := make(chan os.Signal, 1)
	signal.Notify(sig, os.Interrupt, syscall.SIGTERM)
	go func() {
		<-sig
		restore()
		os.Exit(0)
	}()
	return restore
}
 
// readKeys translates raw bytes into logical key names.
func readKeys(r *bufio.Reader, out chan<- string) {
	defer close(out)
	for {
		c, err := r.ReadByte()
		if err != nil {
			return
		}
		switch c {
		case 'a', 'A':
			out <- "left"
		case 'd', 'D':
			out <- "right"
		case ' ', 'w', 'W':
			out <- "fire"
		case 'q', 'Q':
			out <- "quit"
		case '\r', '\n':
			out <- "enter"
		case 27: // escape sequence, e.g. arrow keys: ESC [ C
			b1, err := r.ReadByte()
			if err != nil {
				return
			}
			if b1 != '[' && b1 != 'O' {
				continue
			}
			b2, err := r.ReadByte()
			if err != nil {
				return
			}
			switch b2 {
			case 'D':
				out <- "left"
			case 'C':
				out <- "right"
			case 'A':
				out <- "fire"
			}
		}
	}
}
 
func render(s *Snapshot, isHost bool, hint string) {
	var b strings.Builder
	line := func(format string, args ...any) {
		fmt.Fprintf(&b, format, args...)
		b.WriteString("\x1b[K\r\n")
	}
	b.WriteString("\x1b[H")
 
	switch s.Phase {
	case "lobby":
		line("")
		line("  === SPACE INVADERS - LOBBY ===")
		line("")
		if isHost && hint != "" {
			line("  Others can join at:  %s", hint)
			line("")
		}
		line("  Players (%d/%d):", len(s.Players), maxPlayers)
		for i, p := range s.Players {
			mark := "  "
			if p.ID == s.You {
				mark = "> "
			}
			line("   %s%s%s%s", mark, playerColors[i%len(playerColors)], p.Name, reset)
		}
		line("")
		if isHost {
			line("  Press ENTER to start the game, Q to quit.")
		} else {
			line("  Waiting for the host to start...  (Q to quit)")
		}
 
	case "over":
		line("")
		line("  *** %s ***", s.Msg)
		line("")
		line("  Reached wave %d", s.Level)
		line("")
		line("  Final scores:")
		sorted := append([]PlayerView(nil), s.Players...)
		sort.Slice(sorted, func(i, j int) bool { return sorted[i].Score > sorted[j].Score })
		for i, p := range sorted {
			line("   %d. %-12s %6d", i+1, p.Name, p.Score)
		}
		line("")
		if isHost {
			line("  Press ENTER to go back to the lobby, Q to quit.")
		} else {
			line("  Waiting for the host...  (Q to quit)")
		}
 
	default: // playing
		drawField(&b, s)
	}
 
	b.WriteString("\x1b[J")
	os.Stdout.WriteString(b.String())
}
 
func buildPanel(s *Snapshot) []string {
	p := []string{"  SPACE INVADERS", fmt.Sprintf("  Level %d", s.Level), ""}
	for i, pl := range s.Players {
		mark := " "
		if pl.ID == s.You {
			mark = ">"
		}
		p = append(p, fmt.Sprintf(" %s%s%s%s", mark, playerColors[i%len(playerColors)], pl.Name, reset))
		if pl.Alive {
			p = append(p, fmt.Sprintf("    %d pts  lives %d", pl.Score, pl.Lives))
		} else {
			p = append(p, fmt.Sprintf("    %d pts  (destroyed)", pl.Score))
		}
	}
	p = append(p, "", "  Left/Right or A/D: move", "  Space: fire", "  Q: quit")
	if s.Msg != "" {
		p = append(p, "", "  "+s.Msg)
	}
	return p
}
 
func drawField(b *strings.Builder, s *Snapshot) {
	grid := make([][]string, H)
	for y := range grid {
		grid[y] = make([]string, W)
		for x := range grid[y] {
			grid[y][x] = " "
		}
	}
	put := func(x, y int, str string) {
		if x >= 0 && x < W && y >= 0 && y < H {
			grid[y][x] = str
		}
	}
	for _, v := range s.Invaders {
		i := v[2] % len(invColors)
		put(v[0], v[1], invColors[i]+invChars[i]+reset)
	}
	for _, v := range s.Bombs {
		put(v[0], v[1], "\x1b[91m!"+reset)
	}
	for _, v := range s.Bullets {
		put(v[0], v[1], "\x1b[97m|"+reset)
	}
	for i, p := range s.Players {
		if !p.Alive || p.Blink {
			continue
		}
		col := playerColors[i%len(playerColors)]
		if p.ID == s.You {
			col = "\x1b[7m" + col // own ship is highlighted
		}
		put(p.X, H-1, col+"A"+reset)
	}
 
	panel := buildPanel(s)
	border := "+" + strings.Repeat("-", W) + "+"
	for r := 0; r < H+2; r++ {
		if r == 0 || r == H+1 {
			b.WriteString(border)
		} else {
			b.WriteString("|")
			b.WriteString(strings.Join(grid[r-1], ""))
			b.WriteString("|")
		}
		if r < len(panel) {
			b.WriteString(panel[r])
		}
		b.WriteString("\x1b[K\r\n")
	}
}
 
// ---------------------------------------------------------------------------
// Helpers & main menu
// ---------------------------------------------------------------------------
 
func sanitizeName(s string) string {
	var out []rune
	for _, c := range strings.TrimSpace(s) {
		if unicode.IsPrint(c) {
			out = append(out, c)
		}
		if len(out) >= maxNameLen {
			break
		}
	}
	if len(out) == 0 {
		return "Player"
	}
	return string(out)
}
 
func localIPs() []string {
	var out []string
	addrs, err := net.InterfaceAddrs()
	if err != nil {
		return nil
	}
	for _, a := range addrs {
		if ipn, ok := a.(*net.IPNet); ok && !ipn.IP.IsLoopback() && ipn.IP.To4() != nil {
			out = append(out, ipn.IP.String())
		}
	}
	return out
}
 
func prompt(r *bufio.Reader, label, def string) string {
	fmt.Print(label)
	if def != "" {
		fmt.Printf("[%s] ", def)
	}
	line, err := r.ReadString('\n')
	if err != nil && line == "" {
		fmt.Println()
		os.Exit(0)
	}
	line = strings.TrimSpace(line)
	if line == "" {
		return def
	}
	return line
}
 
func main() {
	r := bufio.NewReader(os.Stdin)
 
	fmt.Println("=== TERMINAL SPACE INVADERS (multiplayer) ===")
	fmt.Println()
	fmt.Println("  1) Host a game")
	fmt.Println("  2) Join a game")
	fmt.Println()
 
	for {
		switch prompt(r, "Choose 1 or 2: ", "") {
		case "1":
			name := prompt(r, "Your name: ", "Player")
			port := prompt(r, "Port to listen on: ", defaultPort)
			runHost(r, sanitizeName(name), port)
			fmt.Println("Bye!")
			return
		case "2":
			addr := prompt(r, "Host address (e.g. 192.168.1.10:9000): ", "")
			if addr == "" {
				fmt.Println("Please enter an address.")
				continue
			}
			if _, _, err := net.SplitHostPort(addr); err != nil {
				addr = net.JoinHostPort(addr, defaultPort)
			}
			name := prompt(r, "Your name: ", "Player")
			runClient(r, addr, sanitizeName(name))
			fmt.Println("Bye!")
			return
		default:
			fmt.Println("Please type 1 or 2.")
		}
	}
}
