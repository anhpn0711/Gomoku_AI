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
# CÁC TRẠNG THÁI KIỂM THỬ (LEVEL 3)
# ==========================================
TEST_CASES = {
    "1. Trạng thái đầu ván (Trống)": [
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
    ],
    "2. Trạng thái giữa ván (Cân bằng)": [
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,2,0,0,0,0],
        [0,0,0,2,1,1,0,0,0],
        [0,0,0,0,0,1,2,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
    ],
    "3. Trạng thái X sắp thắng (Cần chặn)": [
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,2,0,0,0,0],
        [0,0,0,0,1,0,0,0,0],
        [0,0,0,0,1,2,0,0,0],
        [0,0,0,0,1,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
    ],
    "4. Trạng thái máy O có thể thắng ngay": [
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,1,1,1,0,0,0,0],
        [0,0,0,2,2,2,0,0,0], 
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
    ],
    "5. Trạng thái phức tạp (Nhiều nhánh)": [
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,1,0,0,0,0],
        [0,0,0,2,1,2,0,0,0],
        [0,0,2,1,2,1,0,0,0],
        [0,0,0,1,2,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
        [0,0,0,0,0,0,0,0,0],
    ]
}

# ==========================================
# PHẦN 1: AI SOLVER
# ==========================================
class AISolver:
    def __init__(self, board_snapshot, ai_piece, player_piece, request_id, max_depth, time_limit, mode="hard"):
        self.board = board_snapshot
        self.ai_piece = ai_piece
        self.player_piece = player_piece
        self.request_id = request_id
        self.max_depth = max_depth
        self.time_limit = time_limit
        self.mode = mode 
        
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
                if p != EMPTY: h ^= ZOBRIST_TABLE[r][c][p]
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
        
        if self.mode == "hard":
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

        if self.mode == "hard" and self.current_hash in self.transposition_table:
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
            if self.mode == "hard": self.transposition_table[self.current_hash] = (depth, score, 'EXACT')
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
                
                if self.mode in ["normal", "hard"]:
                    alpha = max(alpha, eval_score)
                    if beta <= alpha:
                        if self.mode == "hard": self.history_heuristic[r][c] += depth ** 2 
                        break 
                    
            flag = 'EXACT' if max_eval > orig_alpha and max_eval < beta else ('LOWERBOUND' if max_eval >= beta else 'UPPERBOUND')
            if not self.timeout_flag and self.mode == "hard": self.transposition_table[self.current_hash] = (depth, max_eval, flag)
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
                
                if self.mode in ["normal", "hard"]:
                    beta = min(beta, eval_score)
                    if beta <= alpha:
                        if self.mode == "hard": self.history_heuristic[r][c] += depth ** 2
                        break 

            flag = 'EXACT' if min_eval > orig_alpha and min_eval < beta else ('LOWERBOUND' if min_eval <= orig_alpha else 'UPPERBOUND')
            if not self.timeout_flag and self.mode == "hard": self.transposition_table[self.current_hash] = (depth, min_eval, flag)
            return min_eval, best_move

    def search(self, cancel_token_func):
        self.start_time = time.time()
        best_move_overall = None
        best_score_overall = 0
        reached_depth = 0

        for depth in range(1, self.max_depth + 1):
            score, move = self.minimax(depth, -math.inf, math.inf, True, None, None, cancel_token_func)
            if self.timeout_flag and best_move_overall is not None:
                break
            if move:
                best_move_overall = move
                best_score_overall = score
            reached_depth = depth
            if score > 5000000: break 

        t_spent = round(time.time() - self.start_time, 3)
        return best_move_overall, best_score_overall, reached_depth, self.nodes_evaluated, self.cache_hits, t_spent


# ==========================================
# PHẦN 2: THREAD-SAFE GUI VỚI HISTORY & TIMER
# ==========================================
class GomokuApp:
    def __init__(self, root):
        self.root = root
        self.root.title("Gomoku - Full Features with AI Move Log")
        self.root.geometry("1150x750")
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

    def reset_score(self):
        self.player_score = 0
        self.ai_score = 0
        self.lbl_score.config(text=f"Bạn: {self.player_score}  -  AI: {self.ai_score}")

    def clear_log(self):
        """Xóa toàn bộ dữ liệu trong bảng log Treeview và Đánh giá"""
        for item in self.log_tree.get_children():
            self.log_tree.delete(item)
        if hasattr(self, 'lbl_ai_status'):
            self.lbl_ai_status.config(text="Trạng thái: Sẵn sàng", fg="#ffffff")
            self.lbl_ai_score_val.config(text="Điểm thế trận: 0", fg="#2ed573")
            self.lbl_ai_judgment.config(text="Nhận định: Trận đấu cân bằng", fg="#a4b0be")

    def stop_game(self):
        with self.state_lock:
            self.ai_request_id += 1 
            self.game_active = False
            self.ai_is_thinking = False
            
            self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
            self.move_history.clear()
            self.clear_log() 
            self.last_move_ui = None
            self.winning_line_ui = []
            
            self.btn_x.config(state=tk.NORMAL)
            self.btn_o.config(state=tk.NORMAL)
            self.lbl_stats.config(text="")
            
            self.stop_timer()
            self.lbl_timer.config(text="Thời gian: 00:00")
            
            self.draw_board()
            self.update_status("Đã hủy ván. Vui lòng chọn quân cờ!", "#ffa502")

    def undo_move(self):
        with self.state_lock:
            if not self.move_history: return 

            self.ai_request_id += 1
            self.ai_is_thinking = False
            self.game_active = True 
            self.btn_x.config(state=tk.DISABLED)
            self.btn_o.config(state=tk.DISABLED)

            last_piece = self.move_history[-1][2]
            moves_to_undo = 2 if (last_piece == self.ai_piece and len(self.move_history) >= 2) else 1
                
            for _ in range(moves_to_undo):
                if self.move_history:
                    r, c, p = self.move_history.pop()
                    self.board[r][c] = EMPTY
                    
                    children = self.log_tree.get_children()
                    if children:
                        self.log_tree.delete(children[-1])
            
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
            self.lbl_ai_status.config(text="Trạng thái: Chờ bạn di chuyển...", fg="#ffffff")

    def load_test_case(self):
        test_key = self.test_cb_var.get()
        if test_key not in TEST_CASES:
            messagebox.showwarning("Cảnh báo", "Vui lòng chọn một trạng thái kiểm thử hợp lệ!")
            return

        with self.state_lock:
            self.ai_request_id += 1 
            self.game_active = True
            self.ai_is_thinking = False
            
            self.player_piece = X_PIECE
            self.ai_piece = O_PIECE
            self.btn_x.config(state=tk.DISABLED)
            self.btn_o.config(state=tk.DISABLED)

            self.board = copy.deepcopy(TEST_CASES[test_key])
            self.move_history.clear()
            self.clear_log() 
            self.last_move_ui = None
            self.winning_line_ui = []

            x_count = sum(row.count(X_PIECE) for row in self.board)
            o_count = sum(row.count(O_PIECE) for row in self.board)
            
            if x_count == o_count:
                self.current_turn = X_PIECE
                self.update_status("Đã nạp xong! Đến lượt BẠN (X) đi.", "#2ed573")
                self.lbl_ai_status.config(text="Trạng thái: Chờ bạn di chuyển...", fg="#ffffff")
            else:
                self.current_turn = O_PIECE
                self.update_status("Đã nạp xong! Đến lượt AI (O) đi...", "#ffa502")
            
            self.stop_timer()
            self.lbl_timer.config(text="Thời gian: 00:00")
            self.lbl_stats.config(text="Đã tải dữ liệu kiểm thử. Nhấn vào bàn cờ hoặc đợi AI đánh.")
            self.draw_board()

            if self.current_turn == self.ai_piece:
                self._trigger_ai_thread_locked()

    def start_game(self, player_piece):
        with self.state_lock:
            self.ai_request_id += 1
            self.board = [[EMPTY for _ in range(BOARD_SIZE)] for _ in range(BOARD_SIZE)]
            self.move_history.clear()
            self.clear_log() 
            
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
                self.lbl_ai_status.config(text="Trạng thái: Chờ bạn di chuyển...", fg="#ffffff")

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
            self.lbl_ai_status.config(text="Trạng thái: Game Kết Thúc", fg="#2ed573")
            self.lbl_ai_judgment.config(text="Nhận định: Bạn đã thắng ván này!", fg="#2ed573")
            messagebox.showinfo("Kết quả", "Bạn đã chiến thắng!")
        elif winner_piece == self.ai_piece:
            self.ai_score += 1
            self.update_status("AI ĐÃ THẮNG!", "#ff4757")
            self.lbl_ai_status.config(text="Trạng thái: Game Kết Thúc", fg="#ff4757")
            self.lbl_ai_judgment.config(text="Nhận định: AI hạ gục người chơi!", fg="#ff4757")
            messagebox.showinfo("Kết quả", "AI đã chiến thắng!")
        else:
            self.update_status("VÁN CỜ HÒA!", "#ffa502")
            self.lbl_ai_status.config(text="Trạng thái: Game Kết Thúc", fg="#ffa502")
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
                
                pos_str = f"{chr(65 + c)}{r + 1}"
                self.log_tree.insert("", "end", values=(len(self.move_history), "Người", pos_str, "-", "-"))
                self.log_tree.yview_moveto(1.0) 

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
        
        self.lbl_ai_status.config(text="Trạng thái: AI đang suy nghĩ...", fg="#ffa502")
        
        board_snapshot = copy.deepcopy(self.board)
        current_mode_text = self.mode_var.get()
        if "Easy" in current_mode_text: logic_mode = "easy"
        elif "Normal" in current_mode_text: logic_mode = "normal"
        else: logic_mode = "hard"

        t = threading.Thread(
            target=self.run_ai_logic, 
            args=(board_snapshot, self.ai_piece, self.player_piece, current_req_id, self.depth_var.get(), self.time_var.get(), logic_mode), 
            daemon=True
        )
        t.start()
        self.update_status(f"AI đang phân tích ({logic_mode})...", "#ffa502")

    def run_ai_logic(self, board_snapshot, ai_p, pl_p, req_id, d_limit, t_limit, mode):
        solver = AISolver(board_snapshot, ai_p, pl_p, req_id, d_limit, t_limit, mode)
        best_move, best_score, depth, nodes, hits, t_spent = solver.search(self.get_cancel_token)
        self.root.after(0, self.apply_ai_move, best_move, best_score, req_id, depth, nodes, hits, t_spent)

    def apply_ai_move(self, move, best_score, req_id, depth, nodes, hits, t_spent):
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
                
                display_score = best_score
                if best_score > 5000000: display_score = "Thắng tuyệt đối!"
                elif best_score < -5000000: display_score = "Thua tuyệt đối!"
                
                self.lbl_stats.config(text=f"Score: {display_score} | Depth: {depth} | Nodes: {nodes} | TT Cache: {hits} | Time: {t_spent}s")

                # Cập nhật thông tin vào Dashboard đánh giá bên phải
                self.lbl_ai_status.config(text="Trạng thái: Đang đợi Bạn đi...", fg="#2ed573")
                self.lbl_ai_score_val.config(text=f"Điểm thế trận: {display_score}", fg="#5352ed" if isinstance(best_score, str) else ("#ff4757" if best_score > 500 else "#2ed573"))
                
                if isinstance(best_score, (int, float)):
                    if best_score > 10000:
                        judgment = "AI đang ép sân rất mạnh!"
                        j_color = "#ff4757"
                    elif best_score > 500:
                        judgment = "AI lợi thế chủ động công."
                        j_color = "#ffa502"
                    elif best_score < -10000:
                        judgment = "Nguy hiểm! Bạn đang áp đảo AI."
                        j_color = "#2ed573"
                    elif best_score < -500:
                        judgment = "Bạn đang giữ thế chủ động."
                        j_color = "#2ed573"
                    else:
                        judgment = "Thế trận cân bằng giằng co."
                        j_color = "#a4b0be"
                else:
                    judgment = "Trận đấu đã ngã ngũ cục diện!"
                    j_color = "#ff4757"
                self.lbl_ai_judgment.config(text=f"Nhận định: {judgment}", fg=j_color)

                # Ghi nhận nước đi kèm Điểm số đánh giá + Thời gian xử lý của AI vào bảng Log UI Treeview
                pos_str = f"{chr(65 + c)}{r + 1}"
                self.log_tree.insert("", "end", values=(len(self.move_history), "AI", pos_str, display_score, f"{t_spent}s"))
                self.log_tree.yview_moveto(1.0) 

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
        
        style.configure("Treeview", background="#2f3542", foreground="white", fieldbackground="#2f3542", rowheight=25, font=("Consolas", 10))
        style.configure("Treeview.Heading", background="#1e272e", foreground="white", font=("Arial", 10, "bold"))
        style.map("Treeview.Heading", background=[('active', '#2f3542')])

    def setup_ui(self):
        header = ttk.Frame(self.root, style="Dark.TFrame")
        header.pack(fill=tk.X, pady=10)

        # Hàng 1: Cấu hình tham số AI
        config_frame = ttk.Frame(header, style="Dark.TFrame")
        config_frame.pack(pady=5)
        
        tk.Label(config_frame, text="Depth:", bg="#121212", fg="white").pack(side=tk.LEFT)
        self.depth_var = tk.IntVar(value=4)
        ttk.Spinbox(config_frame, from_=2, to=8, textvariable=self.depth_var, width=3).pack(side=tk.LEFT)
        
        tk.Label(config_frame, text="Time(s):", bg="#121212", fg="white").pack(side=tk.LEFT, padx=(10, 0))
        self.time_var = tk.DoubleVar(value=2.0)
        ttk.Spinbox(config_frame, from_=0.5, to=10.0, increment=0.5, textvariable=self.time_var, width=4).pack(side=tk.LEFT)

        tk.Label(config_frame, text="Mode:", bg="#121212", fg="white").pack(side=tk.LEFT, padx=(10, 0))
        self.mode_var = tk.StringVar(value="Normal (Minimax + Alpha-Beta)")
        cb_mode = ttk.Combobox(config_frame, textvariable=self.mode_var, state="readonly", width=30)
        cb_mode['values'] = [
            "Easy (Chỉ Minimax)",
            "Normal (Minimax + Alpha-Beta)",
            "Hard (Alpha-Beta + Bảng băm)"
        ]
        cb_mode.pack(side=tk.LEFT)

        # Hàng 2: Chọn phe chọn quân
        btn_frame = ttk.Frame(header, style="Dark.TFrame")
        btn_frame.pack(pady=5)
        self.btn_x = tk.Button(btn_frame, text="Chơi X (Đi trước)", bg="#ff4757", fg="white", command=lambda: self.start_game(X_PIECE))
        self.btn_x.pack(side=tk.LEFT, padx=10)
        self.btn_o = tk.Button(btn_frame, text="Chơi O (Đi sau)", bg="#1e90ff", fg="white", command=lambda: self.start_game(O_PIECE))
        self.btn_o.pack(side=tk.LEFT, padx=10)

        # Hàng 3: Các nút chức năng điều khiển hành động
        action_frame = ttk.Frame(header, style="Dark.TFrame")
        action_frame.pack(pady=5)
        tk.Button(action_frame, text="↶ Lùi bước (Undo)", bg="#2f3542", fg="white", command=self.undo_move).pack(side=tk.LEFT, padx=5)
        tk.Button(action_frame, text="⏹ Dừng/Reset Trận", bg="#2f3542", fg="white", command=self.stop_game).pack(side=tk.LEFT, padx=5)
        tk.Button(action_frame, text="🔄 Reset Tỉ số", bg="#2f3542", fg="white", command=self.reset_score).pack(side=tk.LEFT, padx=5)
        # Nút mới được thêm vào đây:
        tk.Button(action_frame, text="🗑 Xóa Log", bg="#2f3542", fg="white", command=self.clear_log).pack(side=tk.LEFT, padx=5)

        # Hàng 4: Bộ kiểm thử Test Cases (Level 3)
        test_frame = ttk.Frame(header, style="Dark.TFrame")
        test_frame.pack(pady=5)
        tk.Label(test_frame, text="Level 3 Test:", bg="#121212", fg="white").pack(side=tk.LEFT)
        self.test_cb_var = tk.StringVar()
        test_cb = ttk.Combobox(test_frame, textvariable=self.test_cb_var, state="readonly", width=35)
        test_cb['values'] = list(TEST_CASES.keys())
        if len(TEST_CASES) > 0: test_cb.current(0)
        test_cb.pack(side=tk.LEFT, padx=5)
        tk.Button(test_frame, text="Nạp bàn cờ", bg="#f39c12", fg="white", command=self.load_test_case).pack(side=tk.LEFT)

        # Trạng thái tổng quát bên trên bàn cờ
        self.lbl_score = tk.Label(header, text="Bạn: 0  -  AI: 0", font=("Consolas", 18, "bold"), bg="#121212", fg="#2ed573")
        self.lbl_score.pack(pady=5)
        
        self.lbl_timer = tk.Label(header, text="Thời gian: 00:00", font=("Consolas", 14, "bold"), bg="#121212", fg="#ffdd59")
        self.lbl_timer.pack(pady=2)
        
        self.lbl_status = tk.Label(header, text="Vui lòng chọn quân cờ hoặc nạp bàn cờ kiểm thử", font=("Arial", 14), bg="#121212", fg="#ffa502")
        self.lbl_status.pack()

        self.lbl_stats = tk.Label(header, text="", font=("Consolas", 10), bg="#121212", fg="#a4b0be")
        self.lbl_stats.pack()

        # --- PHẦN THÂN GIAO DIỆN CHIA ĐÔI (MAIN BODY SPLIT) ---
        main_body = ttk.Frame(self.root, style="Dark.TFrame")
        main_body.pack(fill=tk.BOTH, expand=True, padx=20, pady=10)

        # Khu vực Trái: Bàn cờ Canvas
        self.canvas_frame = tk.Frame(main_body, bg="#121212")
        self.canvas_frame.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)
        
        self.canvas = tk.Canvas(self.canvas_frame, bg="#1e272e", highlightthickness=0)
        self.canvas.pack(fill=tk.BOTH, expand=True)
        self.canvas.bind("<Configure>", lambda e: self.draw_board())
        self.canvas.bind("<Button-1>", self.on_canvas_click)

        # Khu vực Phải: Bảng Log Lịch sử bước đi & Đánh giá AI
        log_frame = tk.Frame(main_body, bg="#1e1e24", width=420)
        log_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=False, padx=(15, 0))
        log_frame.pack_propagate(False)

        # --- 1. KHUNG CON ĐÁNH GIÁ THẾ TRẬN AI ---
        eval_lf = tk.LabelFrame(log_frame, text=" ĐÁNH GIÁ THẾ TRẬN & ĐIỂM SỐ ", font=("Arial", 11, "bold"), bg="#1e1e24", fg="#ffdd59", bd=1, relief=tk.SOLID)
        eval_lf.pack(fill=tk.X, pady=(0, 15), padx=5)

        self.lbl_ai_status = tk.Label(eval_lf, text="Trạng thái: Sẵn sàng", font=("Arial", 10), bg="#1e1e24", fg="#ffffff", anchor=tk.W)
        self.lbl_ai_status.pack(fill=tk.X, padx=10, pady=4)

        self.lbl_ai_score_val = tk.Label(eval_lf, text="Điểm thế trận: 0", font=("Arial", 10), bg="#1e1e24", fg="#2ed573", anchor=tk.W)
        self.lbl_ai_score_val.pack(fill=tk.X, padx=10, pady=4)
        
        self.lbl_ai_judgment = tk.Label(eval_lf, text="Nhận định: Trận đấu cân bằng", font=("Arial", 10, "italic"), bg="#1e1e24", fg="#a4b0be", anchor=tk.W)
        self.lbl_ai_judgment.pack(fill=tk.X, padx=10, pady=(4, 8))

        # --- 2. KHUNG CON LỊCH SỬ NƯỚC ĐI (TREEVIEW) ---
        hist_lf = tk.LabelFrame(log_frame, text=" LỊCH SỬ NƯỚC ĐI ", font=("Arial", 11, "bold"), bg="#1e1e24", fg="#ffdd59", bd=1, relief=tk.SOLID)
        hist_lf.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)

        columns = ("no", "player", "pos", "score", "time")
        self.log_tree = ttk.Treeview(hist_lf, columns=columns, show="headings")
        
        self.log_tree.heading("no", text="#")
        self.log_tree.heading("player", text="Bên đi")
        self.log_tree.heading("pos", text="Vị trí")
        self.log_tree.heading("score", text="Điểm AI")
        self.log_tree.heading("time", text="Thời gian")

        self.log_tree.column("no", width=35, anchor=tk.CENTER)
        self.log_tree.column("player", width=65, anchor=tk.CENTER)
        self.log_tree.column("pos", width=60, anchor=tk.CENTER)
        self.log_tree.column("score", width=120, anchor=tk.W)
        self.log_tree.column("time", width=80, anchor=tk.CENTER)

        scrollbar = ttk.Scrollbar(hist_lf, orient=tk.VERTICAL, command=self.log_tree.yview)
        self.log_tree.configure(yscrollcommand=scrollbar.set)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.log_tree.pack(side=tk.LEFT, fill=tk.BOTH, expand=True)

    def update_status(self, text, color):
        self.lbl_status.config(text=text, fg=color)

    def draw_board(self):
        self.canvas.delete("all")
        w, h = self.canvas.winfo_width(), self.canvas.winfo_height()
        if w < 10 or h < 10: return

        margin = 40
        board_size_px = min(w, h) * 0.9 - margin
        self.cell_size = board_size_px / BOARD_SIZE
        self.offset_x = (w - board_size_px) / 2 + margin / 2
        self.offset_y = (h - board_size_px) / 2 + margin / 2

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

        font_size = max(8, int(self.cell_size * 0.3))
        for c in range(BOARD_SIZE):
            x = self.offset_x + c * self.cell_size + self.cell_size / 2
            y = self.offset_y - 15
            self.canvas.create_text(x, y, text=chr(65 + c), fill="#a4b0be", font=("Arial", font_size, "bold"))
            
        for r in range(BOARD_SIZE):
            x = self.offset_x - 15
            y = self.offset_y + r * self.cell_size + self.cell_size / 2
            self.canvas.create_text(x, y, text=str(r + 1), fill="#a4b0be", font=("Arial", font_size, "bold"))

if __name__ == "__main__":
    root = tk.Tk()
    app = GomokuApp(root)
    root.mainloop()