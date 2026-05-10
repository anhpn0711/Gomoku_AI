import tkinter as tk
from tkinter import ttk, messagebox
import time
import math
import random
import threading
import logging
import copy

# --- CẤU HÌNH LOGGING ---
logging.basicConfig(level=logging.DEBUG, format='%(asctime)s [%(threadName)s] %(levelname)s: %(message)s')

BOARD_SIZE = 9
WIN_COUNT = 4
EMPTY = 0
X_PIECE = 1
O_PIECE = 2

ZOBRIST_TABLE = [[[random.getrandbits(64) for _ in range(3)] for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]

# ==========================================
# PHẦN 1: AI SOLVER (GIỮ NGUYÊN)
# ==========================================
class AISolver:
    def __init__(self, board_snapshot, ai_piece, player_piece, request_id, max_depth, time_limit):
        self.board = board_snapshot
        self.ai_piece = ai_piece
        self.player_piece = player_piece
        self.request_id = request_id
        self.max_depth = max_depth
        self.time_limit = time_limit
        
        self.current_hash = self._compute_initial_hash()
        self.transposition_table = {}
        self.history_heuristic = [[0 for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        
        self.nodes_evaluated = 0
        self.cache_hits = 0
        self.start_time = 0
        self.timeout_flag = False

    def _compute_initial_hash(self):
        h = 0
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                p = self.board[r][c]
                if p != EMPTY:
                    h ^= ZOBRIST_TABLE[r][c][p]
        return h

    def make_move(self, r, c, piece):
        self.board[r][c] = piece
        self.current_hash ^= ZOBRIST_TABLE[r][c][piece]

    def undo_move(self, r, c, piece):
        self.board[r][c] = EMPTY
        self.current_hash ^= ZOBRIST_TABLE[r][c][piece]

    def is_full(self):
        for row in self.board:
            if EMPTY in row: return False
        return True

    def check_win_logic(self, r, c, piece):
        directions = [(0, 1), (1, 0), (1, 1), (1, -1)]
        for dr, dc in directions:
            count = 1
            nr, nc = r + dr, c + dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == piece:
                count += 1; nr += dr; nc += dc
            nr, nc = r - dr, c - dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == piece:
                count += 1; nr -= dr; nc -= dc
            if count >= WIN_COUNT: return True
        return False

    def evaluate_line(self, count, open_ends, current_turn):
        if count >= WIN_COUNT: return 1000000
        if count == 3:
            if open_ends == 2: return 50000
            if open_ends == 1: return 10000
        if count == 2:
            if open_ends == 2: return 5000
            if open_ends == 1: return 500
        return 0

    def evaluate_local(self, r, c, piece):
        score = 0
        directions = [(0, 1), (1, 0), (1, 1), (1, -1)]
        for dr, dc in directions:
            count = 1
            open_ends = 0
            nr, nc = r + dr, c + dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == piece:
                count += 1; nr += dr; nc += dc
            if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == EMPTY: open_ends += 1
            nr, nc = r - dr, c - dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == piece:
                count += 1; nr -= dr; nc -= dc
            if 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and self.board[nr][nc] == EMPTY: open_ends += 1
            score += self.evaluate_line(count, open_ends, True)
        return score

    def evaluate_board_incremental(self):
        ai_score = 0
        player_score = 0
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] == self.ai_piece:
                    ai_score += self.evaluate_local(r, c, self.ai_piece)
                elif self.board[r][c] == self.player_piece:
                    player_score += self.evaluate_local(r, c, self.player_piece)
        return ai_score - (player_score * 1.5)

    def get_ordered_moves(self):
        moves = []
        has_piece = False
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                if self.board[r][c] != EMPTY:
                    has_piece = True
                    for i in range(max(0, r-2), min(BOARD_SIZE, r+3)):
                        for j in range(max(0, c-2), min(BOARD_SIZE, c+3)):
                            if self.board[i][j] == EMPTY:
                                moves.append((i, j))
        if not has_piece: return [(BOARD_SIZE//2, BOARD_SIZE//2)]
        
        move_set = list(set(moves))
        def move_score(move):
            r, c = move
            self.board[r][c] = self.ai_piece
            atk_score = self.evaluate_local(r, c, self.ai_piece)
            self.board[r][c] = self.player_piece
            def_score = self.evaluate_local(r, c, self.player_piece)
            self.board[r][c] = EMPTY
            hist_score = self.history_heuristic[r][c]
            return atk_score + def_score * 1.2 + hist_score

        move_set.sort(key=move_score, reverse=True)
        return move_set

    def minimax(self, depth, alpha, beta, is_maximizing, last_r, last_c, cancel_token_func):
        self.nodes_evaluated += 1

        if cancel_token_func() != self.request_id or time.time() - self.start_time > self.time_limit:
            self.timeout_flag = True
            return 0, None

        if self.current_hash in self.transposition_table:
            cached_depth, cached_score, cached_flag = self.transposition_table[self.current_hash]
            if cached_depth >= depth:
                self.cache_hits += 1
                if cached_flag == 'EXACT': return cached_score, None
                elif cached_flag == 'LOWERBOUND': alpha = max(alpha, cached_score)
                elif cached_flag == 'UPPERBOUND': beta = min(beta, cached_score)
                if alpha >= beta: return cached_score, None

        if last_r is not None:
            if not is_maximizing and self.check_win_logic(last_r, last_c, self.ai_piece): return 10000000 + depth, None
            if is_maximizing and self.check_win_logic(last_r, last_c, self.player_piece): return -10000000 - depth, None

        if depth == 0 or self.is_full():
            score = self.evaluate_board_incremental()
            self.transposition_table[self.current_hash] = (depth, score, 'EXACT')
            return score, None

        valid_moves = self.get_ordered_moves()
        best_move = None
        orig_alpha = alpha

        if is_maximizing:
            max_eval = -math.inf
            for r, c in valid_moves:
                self.make_move(r, c, self.ai_piece)
                eval_score, _ = self.minimax(depth - 1, alpha, beta, False, r, c, cancel_token_func)
                self.undo_move(r, c, self.ai_piece)
                
                if self.timeout_flag: break

                if eval_score > max_eval:
                    max_eval = eval_score
                    best_move = (r, c)
                alpha = max(alpha, eval_score)
                if beta <= alpha:
                    self.history_heuristic[r][c] += depth ** 2 
                    break
                    
            flag = 'EXACT' if max_eval > orig_alpha and max_eval < beta else ('LOWERBOUND' if max_eval >= beta else 'UPPERBOUND')
            if not self.timeout_flag: self.transposition_table[self.current_hash] = (depth, max_eval, flag)
            return max_eval, best_move
        else:
            min_eval = math.inf
            for r, c in valid_moves:
                self.make_move(r, c, self.player_piece)
                eval_score, _ = self.minimax(depth - 1, alpha, beta, True, r, c, cancel_token_func)
                self.undo_move(r, c, self.player_piece)
                
                if self.timeout_flag: break

                if eval_score < min_eval:
                    min_eval = eval_score
                    best_move = (r, c)
                beta = min(beta, eval_score)
                if beta <= alpha:
                    self.history_heuristic[r][c] += depth ** 2
                    break

            flag = 'EXACT' if min_eval > orig_alpha and min_eval < beta else ('LOWERBOUND' if min_eval <= orig_alpha else 'UPPERBOUND')
            if not self.timeout_flag: self.transposition_table[self.current_hash] = (depth, min_eval, flag)
            return min_eval, best_move

    def search(self, cancel_token_func):
        self.start_time = time.time()
        best_move_overall = None
        reached_depth = 0

        for depth in range(1, self.max_depth + 1):
            score, move = self.minimax(depth, -math.inf, math.inf, True, None, None, cancel_token_func)
            if self.timeout_flag and best_move_overall is not None:
                break
            if move:
                best_move_overall = move
            reached_depth = depth
            if score > 5000000: break

        t_spent = round(time.time() - self.start_time, 3)
        return best_move_overall, reached_depth, self.nodes_evaluated, self.cache_hits, t_spent


# ==========================================
# PHẦN 2: THREAD-SAFE GUI VỚI HISTORY & UNDO & TIMER
# ==========================================
class GomokuApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Gomoku - Thread-Safe & Features")
        self.root.geometry("800x950")
        self.root.configure(bg="#121212")
        
        self.state_lock = threading.Lock()
        
        self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
        self.move_history = [] 
        
        self.player_piece = X_PIECE
        self.ai_piece = O_PIECE
        self.current_turn = X_PIECE
        self.game_active = False
        self.ai_request_id = 0
        self.ai_is_thinking = False
        
        self.player_score = 0
        self.ai_score = 0
        
        self.last_move_ui = None
        self.winning_line_ui = []
        
        self.cell_size = 0
        self.offset_x = 0
        self.offset_y = 0

        # --- TIMER VARIABLES ---
        self.timer_running = False
        self.start_time_real = 0
        self.timer_id = None

        self.setup_styles()
        self.setup_ui()

    def get_cancel_token(self):
        with self.state_lock:
            return self.ai_request_id

    def check_win_logic(self, board, r, c, piece):
        directions = [(0, 1), (1, 0), (1, 1), (1, -1)]
        for dr, dc in directions:
            count = 1
            line = [(r, c)]
            nr, nc = r + dr, c + dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and board[nr][nc] == piece:
                count += 1; line.append((nr, nc)); nr += dr; nc += dc
            nr, nc = r - dr, c - dc
            while 0 <= nr < BOARD_SIZE and 0 <= nc < BOARD_SIZE and board[nr][nc] == piece:
                count += 1; line.append((nr, nc)); nr -= dr; nc -= dc
            if count >= WIN_COUNT: return True, line
        return False, []

    def is_board_full(self, board):
        for row in board:
            if EMPTY in row: return False
        return True

    # --------------- TÍNH NĂNG BẤM GIỜ ---------------
    def check_and_start_timer(self):
        if not self.timer_running:
            self.timer_running = True
            self.start_time_real = time.time()
            self.update_timer()

    def update_timer(self):
        if self.timer_running:
            elapsed = int(time.time() - self.start_time_real)
            mins, secs = divmod(elapsed, 60)
            self.lbl_timer.config(text=f"Thời gian: {mins:02d}:{secs:02d}")
            self.timer_id = self.root.after(1000, self.update_timer)

    def stop_timer(self):
        self.timer_running = False
        if self.timer_id:
            self.root.after_cancel(self.timer_id)
            self.timer_id = None

    # --------------- TÍNH NĂNG RESET & UNDO ---------------
    
    def reset_score(self):
        """Xóa trắng tỉ số hai bên."""
        self.player_score = 0
        self.ai_score = 0
        self.lbl_score.config(text=f"Bạn: {self.player_score}  -  AI: {self.ai_score}")
        logging.info("Đã reset tỉ số về 0-0")

    def stop_game(self):
        """Ngắt ván cờ hiện tại, dọn dẹp bàn cờ."""
        with self.state_lock:
            self.ai_request_id += 1 
            self.game_active = False
            self.ai_is_thinking = False
            
            self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
            self.move_history.clear()
            self.last_move_ui = None
            self.winning_line_ui = []
            
            self.btn_x.config(state=tk.NORMAL)
            self.btn_o.config(state=tk.NORMAL)
            self.lbl_stats.config(text="")
            
            self.stop_timer()
            self.lbl_timer.config(text="Thời gian: 00:00")
            
            self.draw_board()
            self.update_status("Đã hủy ván. Vui lòng chọn quân cờ!", "#ffa502")
            logging.info("Đã dừng/reset trận đấu bằng tay.")

    def undo_move(self):
        """Lùi lại 1 bước đi. Nếu AI đã đi, lùi 2 bước để tới lượt mình."""
        with self.state_lock:
            if not self.move_history:
                return 

            self.ai_request_id += 1
            self.ai_is_thinking = False
            
            self.game_active = True 
            self.btn_x.config(state=tk.DISABLED)
            self.btn_o.config(state=tk.DISABLED)

            last_piece = self.move_history[-1][2]
            
            moves_to_undo = 1
            if last_piece == self.ai_piece and len(self.move_history) >= 2:
                moves_to_undo = 2
                
            for _ in range(moves_to_undo):
                if self.move_history:
                    r, c, p = self.move_history.pop()
                    self.board[r][c] = EMPTY
            
            self.current_turn = self.player_piece
            
            if self.move_history:
                self.last_move_ui = (self.move_history[-1][0], self.move_history[-1][1])
            else:
                self.last_move_ui = None
                self.stop_timer()
                self.lbl_timer.config(text="Thời gian: 00:00")
                
            self.winning_line_ui = []
            self.draw_board()
            self.update_status("Đã lùi bước. Đến lượt BẠN!", "#2ed573")
            logging.info(f"Undo thực hiện. Đã lùi {moves_to_undo} bước.")

    # -----------------------------------------------------------

    def start_game(self, player_piece):
        with self.state_lock:
            self.ai_request_id += 1
            
            self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
            self.move_history.clear()
            
            self.player_piece = player_piece
            self.ai_piece = O_PIECE if player_piece == X_PIECE else X_PIECE
            self.current_turn = X_PIECE
            self.game_active = True
            self.ai_is_thinking = False
            
            self.last_move_ui = None
            self.winning_line_ui = []
            
            self.btn_x.config(state=tk.DISABLED)
            self.btn_o.config(state=tk.DISABLED)
            self.lbl_stats.config(text="")
            
            self.stop_timer()
            self.lbl_timer.config(text="Thời gian: 00:00")
            
            self.draw_board()

            if self.ai_piece == X_PIECE:
                self._trigger_ai_thread_locked()
            else:
                self.update_status("Lượt của BẠN!", "#2ed573")

    def end_game(self, winner_piece, last_r, last_c):
        self.game_active = False
        self.ai_request_id += 1 
        self.ai_is_thinking = False
        self.stop_timer()
        
        self.btn_x.config(state=tk.NORMAL)
        self.btn_o.config(state=tk.NORMAL)

        if winner_piece != EMPTY and last_r is not None:
            _, line = self.check_win_logic(self.board, last_r, last_c, winner_piece)
            self.winning_line_ui = line

        if winner_piece == self.player_piece:
            self.player_score += 1
            self.update_status("BẠN ĐÃ THẮNG!", "#2ed573")
            messagebox.showinfo("Kết quả", "Bạn đã chiến thắng!")
        elif winner_piece == self.ai_piece:
            self.ai_score += 1
            self.update_status("AI ĐÃ THẮNG!", "#ff4757")
            messagebox.showinfo("Kết quả", "AI đã chiến thắng!")
        else:
            self.update_status("VÁN CỜ HÒA!", "#ffa502")
            messagebox.showinfo("Kết quả", "Hòa!")

        self.draw_board()
        self.lbl_score.config(text=f"Bạn: {self.player_score}  -  AI: {self.ai_score}")

    def on_canvas_click(self, event):
        with self.state_lock:
            if not self.game_active or self.ai_is_thinking or self.current_turn != self.player_piece: 
                return
            
            c = int((event.x - self.offset_x) // self.cell_size)
            r = int((event.y - self.offset_y) // self.cell_size)

            if 0 <= r < BOARD_SIZE and 0 <= c < BOARD_SIZE:
                if self.board[r][c] != EMPTY: return
                
                self.board[r][c] = self.player_piece
                self.move_history.append((r, c, self.player_piece)) 
                self.last_move_ui = (r, c)
                self.current_turn = self.ai_piece 
                
                self.check_and_start_timer()
                
                self.draw_board()

                is_win, _ = self.check_win_logic(self.board, r, c, self.player_piece)
                if is_win:
                    self.end_game(self.player_piece, r, c)
                elif self.is_board_full(self.board):
                    self.end_game(EMPTY, None, None)
                else:
                    self._trigger_ai_thread_locked()

    def _trigger_ai_thread_locked(self):
        self.ai_request_id += 1
        current_req_id = self.ai_request_id
        self.ai_is_thinking = True
        
        board_snapshot = copy.deepcopy(self.board)
        t = threading.Thread(
            target=self.run_ai_logic, 
            args=(board_snapshot, self.ai_piece, self.player_piece, current_req_id, self.depth_var.get(), self.time_var.get()), 
            daemon=True
        )
        t.start()
        self.update_status("AI đang phân tích...", "#ffa502")

    def run_ai_logic(self, board_snapshot, ai_p, pl_p, req_id, d_limit, t_limit):
        solver = AISolver(board_snapshot, ai_p, pl_p, req_id, d_limit, t_limit)
        best_move, depth, nodes, hits, t_spent = solver.search(self.get_cancel_token)
        self.root.after(0, self.apply_ai_move, best_move, req_id, depth, nodes, hits, t_spent)

    def apply_ai_move(self, move, req_id, depth, nodes, hits, t_spent):
        with self.state_lock:
            if not self.game_active or req_id != self.ai_request_id or self.current_turn != self.ai_piece:
                return

            if move:
                r, c = move
                if self.board[r][c] != EMPTY: return
                
                self.board[r][c] = self.ai_piece
                self.move_history.append((r, c, self.ai_piece)) 
                self.last_move_ui = (r, c)
                self.ai_is_thinking = False
                self.current_turn = self.player_piece
                
                self.check_and_start_timer()
                
                self.draw_board()
                self.lbl_stats.config(text=f"Depth: {depth} | Nodes: {nodes} | Cache: {hits} | Time: {t_spent}s")

                is_win, _ = self.check_win_logic(self.board, r, c, self.ai_piece)
                if is_win:
                    self.end_game(self.ai_piece, r, c)
                elif self.is_board_full(self.board):
                    self.end_game(EMPTY, None, None)
                else:
                    self.update_status("Đến lượt BẠN!", "#2ed573")


    # --------------- UI SETUP & DRAWING ---------------
    def setup_styles(self):
        style = ttk.Style()
        style.theme_use("clam")
        style.configure("TButton", font=("Arial", 10, "bold"), padding=5)
        style.configure("Dark.TFrame", background="#121212")

    def setup_ui(self):
        header = ttk.Frame(self.root, style="Dark.TFrame")
        header.pack(fill=tk.X, pady=10)

        config_frame = ttk.Frame(header, style="Dark.TFrame")
        config_frame.pack(pady=5)
        
        tk.Label(config_frame, text="Max Depth:", bg="#121212", fg="white").pack(side=tk.LEFT, padx=5)
        self.depth_var = tk.IntVar(value=5)
        ttk.Spinbox(config_frame, from_=3, to=8, textvariable=self.depth_var, width=5).pack(side=tk.LEFT)
        
        tk.Label(config_frame, text="Time Limit (s):", bg="#121212", fg="white").pack(side=tk.LEFT, padx=10)
        self.time_var = tk.DoubleVar(value=1.5)
        ttk.Spinbox(config_frame, from_=0.5, to=5.0, increment=0.5, textvariable=self.time_var, width=5).pack(side=tk.LEFT)

        btn_frame = ttk.Frame(header, style="Dark.TFrame")
        btn_frame.pack(pady=5)
        self.btn_x = tk.Button(btn_frame, text="Chơi X (Đi trước)", bg="#ff4757", fg="white", command=lambda: self.start_game(X_PIECE))
        self.btn_x.pack(side=tk.LEFT, padx=10)
        self.btn_o = tk.Button(btn_frame, text="Chơi O (Đi sau)", bg="#1e90ff", fg="white", command=lambda: self.start_game(O_PIECE))
        self.btn_o.pack(side=tk.LEFT, padx=10)

        action_frame = ttk.Frame(header, style="Dark.TFrame")
        action_frame.pack(pady=5)
        
        btn_undo = tk.Button(action_frame, text="↶ Lùi bước", bg="#2f3542", fg="white", command=self.undo_move)
        btn_undo.pack(side=tk.LEFT, padx=5)
        
        btn_stop = tk.Button(action_frame, text="⏹ Dừng/Reset Trận", bg="#2f3542", fg="white", command=self.stop_game)
        btn_stop.pack(side=tk.LEFT, padx=5)
        
        btn_score_reset = tk.Button(action_frame, text="🔄 Reset Tỉ số", bg="#2f3542", fg="white", command=self.reset_score)
        btn_score_reset.pack(side=tk.LEFT, padx=5)

        self.lbl_score = tk.Label(header, text="Bạn: 0  -  AI: 0", font=("Consolas", 18, "bold"), bg="#121212", fg="#2ed573")
        self.lbl_score.pack(pady=5)
        
        self.lbl_timer = tk.Label(header, text="Thời gian: 00:00", font=("Consolas", 14, "bold"), bg="#121212", fg="#ffdd59")
        self.lbl_timer.pack(pady=2)
        
        self.lbl_status = tk.Label(header, text="Vui lòng chọn quân cờ", font=("Arial", 14), bg="#121212", fg="#ffa502")
        self.lbl_status.pack()

        self.lbl_stats = tk.Label(header, text="", font=("Consolas", 10), bg="#121212", fg="#a4b0be")
        self.lbl_stats.pack()

        self.canvas_frame = tk.Frame(self.root, bg="#121212")
        self.canvas_frame.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)
        
        self.canvas = tk.Canvas(self.canvas_frame, bg="#1e272e", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)

        self.canvas.bind("<Configure>", lambda e: self.draw_board())
        self.canvas.bind("<Button-1>", self.on_canvas_click)

    def update_status(self, text, color):
        self.lbl_status.config(text=text, fg=color)

    def draw_board(self):
        self.canvas.delete("all")
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w < 10 or h < 10: return

        # Dành lại một khoảng không gian cho toạ độ (Margin)
        margin = 40
        board_size_px = min(w, h) * 0.9 - margin
        self.cell_size = board_size_px / BOARD_SIZE
        self.offset_x = (w - board_size_px) / 2 + margin / 2
        self.offset_y = (h - board_size_px) / 2 + margin / 2

        # Vẽ lưới cờ
        for r in range(BOARD_SIZE):
            for c in range(BOARD_SIZE):
                x1 = self.offset_x + c * self.cell_size
                y1 = self.offset_y + r * self.cell_size
                x2, y2 = x1 + self.cell_size, y1 + self.cell_size

                bg_color = "#57606f"
                if self.last_move_ui == (r, c): bg_color = "#3742fa"
                if (r, c) in self.winning_line_ui: bg_color = "#f1c40f"

                self.canvas.create_rectangle(x1, y1, x2, y2, fill=bg_color, outline="#2f3542", width=2)

                piece = self.board[r][c]
                if piece != EMPTY:
                    pad = self.cell_size * 0.25
                    thickness = max(3, int(self.cell_size * 0.08))
                    if piece == X_PIECE:
                        self.canvas.create_line(x1+pad, y1+pad, x2-pad, y2-pad, fill="#ff4757", width=thickness, capstyle=tk.ROUND)
                        self.canvas.create_line(x1+pad, y2-pad, x2-pad, y1+pad, fill="#ff4757", width=thickness, capstyle=tk.ROUND)
                    elif piece == O_PIECE:
                        self.canvas.create_oval(x1+pad, y1+pad, x2-pad, y2-pad, outline="#1e90ff", width=thickness)

        # Vẽ Toạ độ (A,B,C... và 1,2,3...)
        font_size = max(8, int(self.cell_size * 0.3))
        
        # Cột (A, B, C...)
        for c in range(BOARD_SIZE):
            x = self.offset_x + c * self.cell_size + self.cell_size / 2
            y = self.offset_y - 15
            self.canvas.create_text(x, y, text=chr(65 + c), fill="#a4b0be", font=("Arial", font_size, "bold"))
            
        # Hàng (1, 2, 3...)
        for r in range(BOARD_SIZE):
            x = self.offset_x - 15
            y = self.offset_y + r * self.cell_size + self.cell_size / 2
            self.canvas.create_text(x, y, text=str(r + 1), fill="#a4b0be", font=("Arial", font_size, "bold"))

if __name__ == "__main__":
    root = tk.Tk()
    app = GomokuApp(root)
    root.mainloop()