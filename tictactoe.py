import tkinter as tk
import math
import collections
from tkinter import messagebox, ttk

# ----------------------------------------------------------------------
# 게임 설정 상수 (전역 범위)
# ----------------------------------------------------------------------
HEX_SIZE = 40
TOTAL_PARTS_PER_HEX = 3
DEFAULT_NUM_PLAYERS = 4
DEFAULT_GRID_SIZE = 3
DEFAULT_WINNING_LENGTH = 3
MIN_SETTINGS_WIDTH = 750
WINNING_TYPE_ANY_VERTEX = "일반 모드"
WINNING_TYPE_EDGE_ONLY = "면 모드"
WINNING_TYPE_VERTEX_ONLY = "꼭짓점 모드"
WINNING_TYPE_OPTIONS = [WINNING_TYPE_ANY_VERTEX, WINNING_TYPE_EDGE_ONLY, WINNING_TYPE_VERTEX_ONLY]
DEFAULT_WINNING_TYPE = WINNING_TYPE_ANY_VERTEX
DEFAULT_PLAYER_COLORS = {'P1': 'blue', 'P2': 'red', 'P3': 'green', 'P4': 'purple'}
DEFAULT_PLAYERS = ['P1', 'P2', 'P3', 'P4']

# 캔버스 여백 (Canvas Padding) 상수를 여기에 정의합니다.
CANVAS_PADDING = HEX_SIZE  # 캔버스 여백 (육각형 크기만큼 충분히 줌) <--- 여기!

# ----------------------------------------------------------------------
# 게임 상태 전역 변수 (초기화 함수에서 관리)
# ----------------------------------------------------------------------
GRID_SIZE_N = DEFAULT_GRID_SIZE
GRID_ROWS = GRID_SIZE_N
GRID_COLS = GRID_SIZE_N
TOTAL_SPOTS = GRID_ROWS * GRID_COLS * TOTAL_PARTS_PER_HEX
CANVAS_WIDTH = 0
CANVAS_HEIGHT = 0
START_OFFSET_X = 0
START_OFFSET_Y = 0
board = []
players = []
player_colors = {}
num_players = 0
min_win_length = DEFAULT_WINNING_LENGTH
winning_type = DEFAULT_WINNING_TYPE
game_active = False
adjacency_list = []
vertex_to_parts_map = {}
item_to_board_index = {}
board_index_to_item = {}
available_moves_text_id = None
edit_mode_var = None
ai_thinking = False  # AI가 계산 중인지 여부
first_move = True  # 첫 번째 수 여부 확인

# ----------------------------------------------------------------------
# 헬퍼 함수 (좌표 변환, 거리 계산 등)
# ----------------------------------------------------------------------
def flat_to_coords(flat_index):
    if not 0 <= flat_index < TOTAL_SPOTS: return -1, -1, -1
    hex_index = flat_index // TOTAL_PARTS_PER_HEX
    part_index = flat_index % TOTAL_PARTS_PER_HEX
    row = hex_index // GRID_COLS
    col = hex_index % GRID_COLS
    return row, col, part_index

def coords_to_flat(row, col, part_index):
    if not (0 <= row < GRID_ROWS and 0 <= col < GRID_COLS and 0 <= part_index < TOTAL_PARTS_PER_HEX): return -1
    hex_index = row * GRID_COLS + col
    flat_index = hex_index * TOTAL_PARTS_PER_HEX + part_index
    return flat_index

# ----------------------------------------------------------------------
# 캔버스 크기 및 게임판 시작 위치 계산 함수
# ----------------------------------------------------------------------
def calculate_canvas_geometry():
    global CANVAS_WIDTH, CANVAS_HEIGHT, START_OFFSET_X, START_OFFSET_Y
    min_x_rel, max_x_rel = float('inf'), float('-inf')
    min_y_rel, max_y_rel = float('inf'), float('-inf')

    HEX_VERTEX_ANGLES_RAD = [math.radians(a) for a in [90, 30, -30, -90, -150, 150]]
    for r_idx in range(GRID_ROWS):
        for c_idx in range(GRID_COLS):
            q = c_idx - math.floor(r_idx / 2)
            cx_rel = HEX_SIZE * math.sqrt(3) * (q + r_idx / 2.0)
            cy_rel = HEX_SIZE * (3.0 / 2.0) * r_idx
            for angle in HEX_VERTEX_ANGLES_RAD:
                vx_rel = cx_rel + HEX_SIZE * math.cos(angle)
                vy_rel = cy_rel + HEX_SIZE * math.sin(angle)
                min_x_rel = min(min_x_rel, vx_rel)
                max_x_rel = max(max_x_rel, vx_rel)
                min_y_rel = min(min_y_rel, vy_rel)
                max_y_rel = max(max_y_rel, vy_rel)

    required_drawing_width = max_x_rel - min_x_rel
    required_drawing_height = max_y_rel - min_y_rel
    CANVAS_WIDTH = int(required_drawing_width + 2 * CANVAS_PADDING)
    CANVAS_HEIGHT = int(required_drawing_height + 2 * CANVAS_PADDING)
    START_OFFSET_X = CANVAS_PADDING - min_x_rel
    START_OFFSET_Y = CANVAS_PADDING - min_y_rel

# ----------------------------------------------------------------------
# 인접 리스트 계산 함수
# ----------------------------------------------------------------------
def build_adjacency_list(win_type, vertex_to_parts_map):
    adj_list = [[] for _ in range(TOTAL_SPOTS)]
    parts_to_vertex_map = {}
    ROUND_PRECISION = 2

    for vtx, f_list in vertex_to_parts_map.items():
        for f_idx in f_list:
            if f_idx not in parts_to_vertex_map:
                parts_to_vertex_map[f_idx] = set()
            parts_to_vertex_map[f_idx].add(vtx)

    for flat_index1 in range(TOTAL_SPOTS):
        if flat_index1 not in parts_to_vertex_map: continue
        vertices_of_p1 = parts_to_vertex_map[flat_index1]

        for flat_index2 in range(flat_index1 + 1, TOTAL_SPOTS):
            if flat_index2 not in parts_to_vertex_map: continue
            vertices_of_p2 = parts_to_vertex_map[flat_index2]
            shared_vertices = vertices_of_p1.intersection(vertices_of_p2)
            shared_vertices_count = len(shared_vertices)

            if win_type == WINNING_TYPE_ANY_VERTEX:
                if shared_vertices_count >= 1:
                    adj_list[flat_index1].append(flat_index2)
                    adj_list[flat_index2].append(flat_index1)
            elif win_type == WINNING_TYPE_EDGE_ONLY:
                if shared_vertices_count >= 2:
                    adj_list[flat_index1].append(flat_index2)
                    adj_list[flat_index2].append(flat_index1)
            elif win_type == WINNING_TYPE_VERTEX_ONLY:
                if shared_vertices_count == 1:
                    adj_list[flat_index1].append(flat_index2)
                    adj_list[flat_index2].append(flat_index1)

    return adj_list

def build_vertex_to_parts_map():
    vertex_to_parts_map = {}
    ROUND_PRECISION = 2
    hex_perimeter_vertices_rel_unit = [(math.cos(math.radians(a)), math.sin(math.radians(a))) for a in [90, 30, -30, -90, -150, 150]]
    all_vertices_rel_unit = hex_perimeter_vertices_rel_unit + [(0, 0)]
    part_vertex_indices = {0: [6, 0, 1, 2], 1: [6, 2, 3, 4], 2: [6, 4, 5, 0]}

    for row in range(GRID_ROWS):
        for col in range(GRID_COLS):
            q = col - math.floor(row / 2)
            r = row
            cx = START_OFFSET_X + HEX_SIZE * math.sqrt(3) * (q + r / 2.0)
            cy = START_OFFSET_Y + HEX_SIZE * (3.0 / 2.0) * r

            abs_vertices_this_hex = [(cx + HEX_SIZE * vx, cy + HEX_SIZE * vy) for vx, vy in all_vertices_rel_unit]

            for part_index in range(TOTAL_PARTS_PER_HEX):
                flat_index = coords_to_flat(row, col, part_index)
                if flat_index == -1: continue

                vertices_for_part_abs = [abs_vertices_this_hex[v_idx] for v_idx in part_vertex_indices[part_index]]
                for vx, vy in vertices_for_part_abs:
                    rounded_vertex = (round(vx, ROUND_PRECISION), round(vy, ROUND_PRECISION))
                    if rounded_vertex not in vertex_to_parts_map:
                        vertex_to_parts_map[rounded_vertex] = []
                    if flat_index not in vertex_to_parts_map[rounded_vertex]:
                        vertex_to_parts_map[rounded_vertex].append(flat_index)
    return vertex_to_parts_map

# ----------------------------------------------------------------------
# 승리 조건 확인, 무승부 확인, 가능한 수 계산 함수
def check_win_adjacency(board, adjacency_list, min_win_length, last_move_flat_index):
    player_mark = board[last_move_flat_index]
    if player_mark == ' ': return None

    visited = set()
    queue = collections.deque([last_move_flat_index])
    visited.add(last_move_flat_index)
    count = 0

    while queue:
        current_flat_index = queue.popleft()
        count += 1
        if current_flat_index < 0 or current_flat_index >= len(adjacency_list): continue
        for neighbor_flat_index in adjacency_list[current_flat_index]:
            if 0 <= neighbor_flat_index < TOTAL_SPOTS and board[neighbor_flat_index] == player_mark and neighbor_flat_index not in visited:
                visited.add(neighbor_flat_index)
                queue.append(neighbor_flat_index)

    return player_mark if count >= min_win_length else None

def check_draw(board):
    return ' ' not in board

def calculate_available_moves(board):
    """현재 보드 상태에서 놓을 수 있는 칸의 수를 계산합니다."""
    return board.count(' ')

def draw_hexagon_parts(canvas, cx, cy, size, hex_row, hex_col):
    """육각형을 3개의 클릭 가능한 부분 도형으로 나누어 그립니다."""
    # 육각형 꼭지점 계산 (pointy top 기준)
    angles_rad = [math.radians(a) for a in [90, 30, -30, -90, -150, 150]]
    vertices = [(cx + size * math.cos(angle), cy + size * math.sin(angle)) for angle in angles_rad]
    parts_vertices = [[(cx, cy), vertices[0], vertices[1], vertices[2]],
                      [(cx, cy), vertices[2], vertices[3], vertices[4]],
                      [(cx, cy), vertices[4], vertices[5], vertices[0]]]

    # 각 부분 도형 그리기
    for part_index in range(TOTAL_PARTS_PER_HEX):
        # 이 부분 도형에 해당하는 게임 보드의 flat index 계산
        flat_index = coords_to_flat(hex_row, hex_col, part_index)
        if flat_index == -1: continue

        # 초기 색상 설정
        fill_color = "lightgray"

        # Canvas에 polygon 아이템 생성
        poly_id = canvas.create_polygon(parts_vertices[part_index],
                                        outline="black", fill=fill_color, width=1, tags="hex_part")  # 태그 추가

        # 아이템 ID와 보드 인덱스 매핑 저장
        item_to_board_index[poly_id] = flat_index
        board_index_to_item[poly_id] = flat_index

def draw_hexagon_grid(canvas):
    """9개의 육각형 셀을 3x3 격자 형태로 배치하고 각 셀의 부분을 그립니다."""
    for row in range(GRID_ROWS):
        for col in range(GRID_COLS):
            # 해당 (row, col)에 해당하는 육각형 중심 좌표 계산 (staggered layout)
            q = col - math.floor(row / 2)
            r = row

            cx = START_OFFSET_X + HEX_SIZE * math.sqrt(3) * (q + r / 2.0)
            cy = START_OFFSET_Y + HEX_SIZE * (3.0 / 2.0) * r

            # 육각형 셀을 3개의 부분으로 나누어 그립니다.
            draw_hexagon_parts(canvas, cx, cy, HEX_SIZE, row, col)

# ----------------------------------------------------------------------
# 게임 로직 및 UI 이벤트 처리
# ----------------------------------------------------------------------
def startGame():
    global GRID_SIZE_N, GRID_ROWS, GRID_COLS, TOTAL_SPOTS, num_players, players, player_colors, min_win_length, winning_type, board, current_player_index, current_player, game_active, adjacency_list, vertex_to_parts_map, item_to_board_index, board_index_to_item, available_moves_text_id, CANVAS_WIDTH, CANVAS_HEIGHT, START_OFFSET_X, START_OFFSET_Y, edit_mode_var, ai_thinking, first_move

    # 0. 전역 변수 선언 (UnboundLocalError 방지)
    global game_active, ai_thinking, first_move

    # 1. 설정 값 가져오기 및 검증
    try:
        GRID_SIZE_N = int(grid_size_combo.get())
        if not 2 <= GRID_SIZE_N <= 6: raise ValueError("크기 2~6 선택")

        num_players = int(player_count_combo.get())
        if not 2 <= num_players <= len(DEFAULT_PLAYERS): raise ValueError("인원 2~4 선택") # 4인 모드

        min_win_length = int(winning_length_combo.get())
        if not 3 <= min_win_length <= TOTAL_SPOTS: raise ValueError(f"승리 길이는 3~{TOTAL_SPOTS} 사이")

        winning_type = winning_type_combo.get()
        if winning_type not in WINNING_TYPE_OPTIONS: raise ValueError("잘못된 승리 타입")

    except ValueError as e:
        messagebox.showerror("설정 오류", str(e))
        return

    # 2. 게임 보드 크기, 플레이어, UI 관련 변수 초기화 (순서 중요)
    GRID_ROWS = GRID_SIZE_N
    GRID_COLS = GRID_SIZE_N
    TOTAL_SPOTS = GRID_ROWS * GRID_COLS * TOTAL_PARTS_PER_HEX
    board = [' '] * TOTAL_SPOTS
    players = DEFAULT_PLAYERS[:] # 4인 모드
    player_colors = {p: DEFAULT_PLAYER_COLORS.get(p, 'gray') for p in players}
    item_to_board_index = {}
    board_index_to_item = {}
    game_active = True
    current_player_index = 0
    current_player = players[current_player_index]
    ai_thinking = False
    first_move = True # 첫 번째 수 여부 초기화

    # 3. 캔버스 크기 재계산 및 인접 리스트 생성
    calculate_canvas_geometry()
    canvas.config(width=CANVAS_WIDTH, height=CANVAS_HEIGHT)
    vertex_to_parts_map = build_vertex_to_parts_map()
    adjacency_list = build_adjacency_list(winning_type, vertex_to_parts_map)

    # 4. 캔버스 초기화
    canvas.delete("all")

    # 5. 게임 격자 UI 그리기
    draw_hexagon_grid(canvas)

    # 6. 가능한 수 표시 UI 업데이트
    update_available_moves_text()

    # 7. 상태 라벨 업데이트
    status_label.config(text=f"현재 차례: {current_player} ({player_colors[current_player]})")

    # 8. 위젯 상태 설정
    grid_size_combo.config(state="readonly")
    player_count_combo.config(state="readonly")
    winning_length_combo.config(state="readonly")
    winning_type_combo.config(state="readonly")
    edit_mode_check.config(state="normal")  # 수정 모드 체크 활성화 (4인 모드에서는 사용 가능)


def on_canvas_click(event):
    global current_player_index, current_player, game_active, available_moves_text_id, min_win_length, board, adjacency_list, winning_type
    global first_move # 첫 번째 수

    if not game_active: return

    is_edit_mode = edit_mode_var.get()
    clicked_items = canvas.find_closest(event.x, event.y)
    if not clicked_items: return

    item_id = clicked_items[0]

    if item_id in item_to_board_index:
        flat_index = item_to_board_index[item_id]

        # 수정 모드가 켜져 있고, 클릭한 칸이 비어있지 않으면 -> 칸 비우기
        if is_edit_mode and board[flat_index] != ' ':
             # 보드 상태 업데이트
             board[flat_index] = ' '
             # Canvas 그래픽 업데이트 (기본 색상으로 되돌림)
             canvas.itemconfig(item_id, fill="lightgray") # 초기 빈 칸 색상

             # 남은 수 텍스트 업데이트
             update_available_moves_text()

             # 수정 모드에서는 차례 변경이나 승리/무승부 체크를 하지 않음
             return # 수정 작업 후 함수 종료


        # 수정 모드가 꺼져 있거나 (기존 로직), 수정 모드 중 빈 칸을 클릭했으면 -> 일반 게임 진행
        if not is_edit_mode and board[flat_index] == ' ':
            board[flat_index] = current_player
            canvas.itemconfig(item_id, fill=player_colors[current_player])

            temp_winning_type = winning_type # 임시로 저장
            if first_move:
                # 첫 번째 수일 경우, 승리 조건을 '면으로만 인접 승리'로 임시 변경
                temp_adj_list = build_adjacency_list(WINNING_TYPE_EDGE_ONLY, vertex_to_parts_map)
            else:
                # 첫 번째 수가 아니면 원래 승리 타입의 인접 리스트 사용
                temp_adj_list = adjacency_list


            winner = check_win_adjacency(board, temp_adj_list, min_win_length, last_move_flat_index=flat_index)

            # 첫 번째 수 여부 업데이트 및 승리 타입 복원
            if first_move:
                first_move = False # 첫 번째 수 끝

            if winner:
                game_active = False
                status_label.config(text=f"축하합니다! {winner} 승리! (연결 {min_win_length}, {winning_type})")
                grid_size_combo.config(state="readonly")
                player_count_combo.config(state="readonly")
                winning_length_combo.config(state="readonly")
                winning_type_combo.config(state="readonly")
                edit_mode_check.config(state="disabled")
            elif check_draw(board):  # check_draw 함수에 인자 board 전달
                game_active = False
                status_label.config(text="무승부!")
                grid_size_combo.config(state="readonly")
                player_count_combo.config(state="readonly")
                winning_length_combo.config(state="readonly")
                winning_type_combo.config(state="readonly")
                edit_mode_check.config(state="disabled")
            else:
                next_player()
            update_available_moves_text()

def update_available_moves_text():
    available_moves = calculate_available_moves(board)
    canvas.itemconfig(available_moves_text_id, text=f"남은 수: {available_moves}")

def next_player():
    global current_player_index, current_player
    current_player_index = (current_player_index + 1) % num_players
    current_player = players[current_player_index]
    status_label.config(text=f"현재 차례: {current_player} ({player_colors[current_player]})")


def reset_game():
    global GRID_SIZE_N, GRID_ROWS, GRID_COLS, TOTAL_SPOTS, CANVAS_WIDTH, CANVAS_HEIGHT, START_OFFSET_X, START_OFFSET_Y
    global board, players, player_colors, num_players, min_win_length, winning_type, game_active, adjacency_list, vertex_to_parts_map
    global item_to_board_index, board_index_to_item, available_moves_text_id, edit_mode_var, first_move

    # 1. 게임 설정 관련 전역 변수 초기화
    GRID_SIZE_N = DEFAULT_GRID_SIZE
    GRID_ROWS = GRID_SIZE_N
    GRID_COLS = GRID_SIZE_N
    TOTAL_SPOTS = GRID_ROWS * GRID_COLS * 3

    # 2. 게임 내용 관련 전역 변수 초기화
    board = [' '] * TOTAL_SPOTS
    players = DEFAULT_PLAYERS[:]
    player_colors = {p: DEFAULT_PLAYER_COLORS.get(p, 'gray') for p in players} # 색상 초기화 추가
    num_players = DEFAULT_NUM_PLAYERS
    min_win_length = DEFAULT_WINNING_LENGTH
    winning_type = DEFAULT_WINNING_TYPE
    game_active = False
    adjacency_list = []
    vertex_to_parts_map = {}
    item_to_board_index = {}
    board_index_to_item = {}
    available_moves_text_id = None
    edit_mode_var = tk.BooleanVar(value=False)
    first_move = True # 리셋 시 첫 번째 수

    # 3. 캔버스 초기화
    calculate_canvas_geometry()
    canvas.delete("all")

    # 4. 콤보 박스 및 체크 버튼 초기화
    grid_size_combo.config(state="readonly")
    grid_size_combo.set(str(DEFAULT_GRID_SIZE))
    player_count_combo.config(state="readonly")
    player_count_combo.set(str(DEFAULT_NUM_PLAYERS))
    winning_length_combo.config(state="readonly")
    winning_length_combo.set(str(DEFAULT_WINNING_LENGTH))
    winning_type_combo.config(state="readonly")
    winning_type_combo.set(DEFAULT_WINNING_TYPE)
    edit_mode_check.config(state="normal")  # "수정 모드" 체크 활성화
    edit_mode_var.set(False) # 체크 해제 상태로

    # 5. 상태 라벨 초기화
    status_label.config(text="설정을 선택하고 게임 시작")

root = tk.Tk()
root.title("육각형 틱택토 (설정 가능, 면/꼭짓점 인접 승리)")

# 설정 프레임
settings_frame = tk.Frame(root)
settings_frame.pack(pady=10)

# 1행 설정
frame1 = tk.Frame(settings_frame)
frame1.pack(side=tk.TOP, fill=tk.X, padx=5, pady=2)

grid_size_label = tk.Label(frame1, text="격자 크기 (NxN):", font=('Arial', 12))
grid_size_label.pack(side=tk.LEFT, padx=5)
grid_size_combo = ttk.Combobox(frame1, values=[str(i) for i in range(2, 7)], state="readonly", width=3)
grid_size_combo.set(str(DEFAULT_GRID_SIZE))
grid_size_combo.pack(side=tk.LEFT, padx=5)

player_count_label = tk.Label(frame1, text="참여 인원:", font=('Arial', 12))
player_count_label.pack(side=tk.LEFT, padx=5)
player_count_combo = ttk.Combobox(frame1, values=[str(i) for i in range(2, len(DEFAULT_PLAYERS) + 1)], state="readonly", width=3)
player_count_combo.set(str(DEFAULT_NUM_PLAYERS))
player_count_combo.pack(side=tk.LEFT, padx=5)

# 2행 설정
frame2 = tk.Frame(settings_frame)
frame2.pack(side=tk.TOP, fill=tk.X, padx=5, pady=2)

winning_length_label = tk.Label(frame2, text="승리 연결 개수:", font=('Arial', 12))
winning_length_label.pack(side=tk.LEFT, padx=5)
winning_length_combo = ttk.Combobox(frame2, values=[str(i) for i in range(3, 11)], state="readonly", width=3)
winning_length_combo.set(str(DEFAULT_WINNING_LENGTH))
winning_length_combo.pack(side=tk.LEFT, padx=5)

winning_type_label = tk.Label(frame2, text="승리 조건:", font=('Arial', 12))
winning_type_label.pack(side=tk.LEFT, padx=5)
winning_type_combo = ttk.Combobox(frame2, values=WINNING_TYPE_OPTIONS, state="readonly", width=15)
winning_type_combo.set(DEFAULT_WINNING_TYPE)
winning_type_combo.pack(side=tk.LEFT, padx=5)

# 3행 설정
frame3 = tk.Frame(settings_frame)
frame3.pack(side=tk.TOP, fill=tk.X, padx=5, pady=2)

edit_mode_var = tk.BooleanVar(value=False) # 수정 모드 변수 초기화
edit_mode_check = tk.Checkbutton(frame3, text="수정 모드", variable=edit_mode_var, font=('Arial', 12))
edit_mode_check.pack(side=tk.LEFT, padx=5)/

# 버튼
start_button = tk.Button(root, text="게임 시작", command=startGame)
start_button.pack(pady=5)

# 캔버스
calculate_canvas_geometry()
canvas = tk.Canvas(root, width=CANVAS_WIDTH, height=CANVAS_HEIGHT, bg="white")
canvas.pack(pady=10)
canvas.bind("<Button-1>", on_canvas_click)

# 상태 라벨
status_label = tk.Label(root, text=f"게임 시작 전, 설정을 선택하세요.", font=('Arial', 15))
status_label.pack(pady=5)

# 다시 시작 버튼
reset_button = tk.Button(root, text="다시 시작", command=reset_game)
reset_button.pack(pady=5)

# 초기화 함수 호출 및 메인 루프 실행
reset_game()
window_width = max(CANVAS_WIDTH + 40, MIN_SETTINGS_WIDTH)
window_height = 700
root.geometry(f"{window_width}x{window_height}")
root.resizable(False, False)

root.mainloop()
