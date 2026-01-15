#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
Ứng dụng Trực Quan Hóa và Phân Tích Đồ Thị
Graph Visualization & Analysis Application
"""

import tkinter as tk
from tkinter import ttk, messagebox, filedialog
import networkx as nx
import matplotlib.pyplot as plt
from matplotlib.backends.backend_tkagg import FigureCanvasTkAgg
from matplotlib.figure import Figure
from collections import deque, defaultdict
import json
from typing import List, Dict, Set, Tuple, Optional
import pickle


# ============ LỚP ĐỒNG THỊ =============
class Graph:
    """Lớp đại diện cho đồ thị"""
    
    def __init__(self, is_directed=False):
        self.is_directed = is_directed
        self.adjacency_list = defaultdict(list)
        self.vertices = set()
        self.edge_list = []
        
    def add_edge(self, u, v, weight=1):
        """Thêm cạnh vào đồ thị"""
        self.vertices.add(u)
        self.vertices.add(v)
        self.adjacency_list[u].append((v, weight))
        if not self.is_directed:
            self.adjacency_list[v].append((u, weight))
        self.edge_list.append((u, v, weight))
        
    def add_vertex(self, v):
        """Thêm đỉnh"""
        self.vertices.add(v)
        if v not in self.adjacency_list:
            self.adjacency_list[v] = []
    
    def to_adjacency_matrix(self):
        """Chuyển đồ thị sang ma trận kề"""
        vertices_list = sorted(list(self.vertices))
        n = len(vertices_list)
        matrix = [[0] * n for _ in range(n)]
        vertex_to_idx = {v: i for i, v in enumerate(vertices_list)}
        
        for u in self.adjacency_list:
            for v, weight in self.adjacency_list[u]:
                i = vertex_to_idx[u]
                j = vertex_to_idx[v]
                matrix[i][j] = weight
                
        return matrix, vertices_list
    
    def from_adjacency_matrix(self, matrix, vertices_list):
        """Tạo đồ thị từ ma trận kề"""
        self.vertices = set(vertices_list)
        self.adjacency_list.clear()
        self.edge_list.clear()
        
        for u in vertices_list:
            self.adjacency_list[u] = []
        
        for i, u in enumerate(vertices_list):
            for j, v in enumerate(vertices_list):
                if matrix[i][j] != 0:
                    weight = matrix[i][j]
                    self.adjacency_list[u].append((v, weight))
                    if (u, v, weight) not in self.edge_list:
                        self.edge_list.append((u, v, weight))
    
    def to_edge_list(self):
        """Chuyển sang danh sách cạnh"""
        return self.edge_list.copy()
    
    def from_edge_list(self, edges):
        """Tạo đồ thị từ danh sách cạnh"""
        self.vertices.clear()
        self.adjacency_list.clear()
        self.edge_list = edges.copy()
        
        for u, v, weight in edges:
            self.add_edge(u, v, weight)
    
    def bfs(self, start):
        """Duyệt theo chiều rộng"""
        visited = set()
        queue = deque([start])
        visited.add(start)
        result = []
        
        while queue:
            vertex = queue.popleft()
            result.append(vertex)
            
            for neighbor, _ in self.adjacency_list[vertex]:
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append(neighbor)
        
        return result
    
    def dfs(self, start):
        """Duyệt theo chiều sâu"""
        visited = set()
        result = []
        
        def dfs_helper(v):
            visited.add(v)
            result.append(v)
            for neighbor, _ in self.adjacency_list[v]:
                if neighbor not in visited:
                    dfs_helper(neighbor)
        
        dfs_helper(start)
        return result
    
    def shortest_path_bfs(self, start, end):
        """Tìm đường đi ngắn nhất sử dụng BFS"""
        if start == end:
            return [start]
        
        visited = {start}
        queue = deque([(start, [start])])
        
        while queue:
            vertex, path = queue.popleft()
            
            for neighbor, _ in self.adjacency_list[vertex]:
                if neighbor == end:
                    return path + [neighbor]
                if neighbor not in visited:
                    visited.add(neighbor)
                    queue.append((neighbor, path + [neighbor]))
        
        return None
    
    def is_bipartite(self):
        """Kiểm tra xem đồ thị có phải 2 phía hay không"""
        if not self.vertices:
            return True
        
        color = {}
        
        def bfs_check(start):
            queue = deque([start])
            color[start] = 0
            
            while queue:
                u = queue.popleft()
                for v, _ in self.adjacency_list[u]:
                    if v not in color:
                        color[v] = 1 - color[u]
                        queue.append(v)
                    elif color[v] == color[u]:
                        return False
            return True
        
        for vertex in self.vertices:
            if vertex not in color:
                if not bfs_check(vertex):
                    return False
        
        return True
    
    def dijkstra(self, start):
        """Thuật toán Dijkstra tìm đường đi ngắn nhất"""
        distances = {v: float('inf') for v in self.vertices}
        distances[start] = 0
        visited = set()
        
        while len(visited) < len(self.vertices):
            min_dist = float('inf')
            min_vertex = None
            
            for v in self.vertices:
                if v not in visited and distances[v] < min_dist:
                    min_dist = distances[v]
                    min_vertex = v
            
            if min_vertex is None:
                break
            
            visited.add(min_vertex)
            
            for neighbor, weight in self.adjacency_list[min_vertex]:
                if neighbor not in visited:
                    distances[neighbor] = min(
                        distances[neighbor],
                        distances[min_vertex] + weight
                    )
        
        return distances
        # ====== PHẦN NÂNG CAO ======
    def prim_mst(self):
        """Thuật toán Prim - Minimum Spanning Tree"""
        if self.is_directed:
            raise ValueError("Prim chỉ áp dụng cho đồ thị vô hướng")

        if not self.vertices:
            return []

        visited = set()
        start = next(iter(self.vertices))
        visited.add(start)
        mst = []

        edges = []
        for v, w in self.adjacency_list[start]:
            edges.append((w, start, v))

        while edges and len(visited) < len(self.vertices):
            edges.sort()
            weight, u, v = edges.pop(0)

            if v in visited:
                continue

            visited.add(v)
            mst.append((u, v, weight))

            for to, w in self.adjacency_list[v]:
                if to not in visited:
                    edges.append((w, v, to))

        return mst

    def kruskal_mst(self):
        """Thuật toán Kruskal - Minimum Spanning Tree"""
        if self.is_directed:
            raise ValueError("Kruskal chỉ áp dụng cho đồ thị vô hướng")

        parent = {}
        rank = {}

        def find(u):
            if parent[u] != u:
                parent[u] = find(parent[u])
            return parent[u]

        def union(u, v):
            ru, rv = find(u), find(v)
            if ru == rv:
                return False
            if rank[ru] < rank[rv]:
                parent[ru] = rv
            else:
                parent[rv] = ru
                if rank[ru] == rank[rv]:
                    rank[ru] += 1
            return True

        for v in self.vertices:
            parent[v] = v
            rank[v] = 0

        mst = []
        edges = sorted(self.edge_list, key=lambda x: x[2])

        for u, v, w in edges:
            if union(u, v):
                mst.append((u, v, w))

        return mst



# ============ ỨNG DỤNG TKINTER =============
class GraphApp:
    """Ứng dụng Tkinter cho đồ thị"""
    
    def __init__(self, root):
        self.root = root
        self.root.title("Graph Visualization & Analysis - Trực Quan Hóa và Phân Tích Đồ Thị")
        self.root.geometry("1200x800")
        
        self.graph = Graph(is_directed=False)
        self.nx_graph = nx.Graph()
        self.pos = {}
        
        self.setup_ui()
    
    def setup_ui(self):
        """Thiết lập giao diện"""
        # Frame chính
        main_frame = ttk.Frame(self.root)
        main_frame.pack(fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # Frame điều khiển bên trái
        control_frame = ttk.Frame(main_frame, width=250)
        control_frame.pack(side=tk.LEFT, fill=tk.BOTH, padx=5, pady=5)
        
        # Frame hiển thị đồ thị bên phải
        display_frame = ttk.Frame(main_frame)
        display_frame.pack(side=tk.RIGHT, fill=tk.BOTH, expand=True, padx=5, pady=5)
        
        # ===== PHẦN ĐIỀU KHIỂN =====
        ttk.Label(control_frame, text="=== THÊM PHẦN TỬ ===", font=('Arial', 10, 'bold')).pack(pady=10)
        
        # Thêm đỉnh
        ttk.Label(control_frame, text="Tên đỉnh:").pack()
        self.vertex_entry = ttk.Entry(control_frame)
        self.vertex_entry.pack(pady=5)
        ttk.Button(control_frame, text="Thêm đỉnh", command=self.add_vertex).pack(pady=5)
        
        # Thêm cạnh
        ttk.Label(control_frame, text="Đỉnh từ:").pack()
        self.from_vertex_entry = ttk.Entry(control_frame)
        self.from_vertex_entry.pack(pady=5)
        
        ttk.Label(control_frame, text="Đỉnh đến:").pack()
        self.to_vertex_entry = ttk.Entry(control_frame)
        self.to_vertex_entry.pack(pady=5)
        
        ttk.Label(control_frame, text="Trọng số:").pack()
        self.weight_entry = ttk.Entry(control_frame)
        self.weight_entry.insert(0, "1")
        self.weight_entry.pack(pady=5)
        
        ttk.Button(control_frame, text="Thêm cạnh", command=self.add_edge).pack(pady=5)
        
        # Loại đồ thị
        ttk.Label(control_frame, text="Loại đồ thị:", font=('Arial', 10)).pack(pady=10)
        self.graph_type_var = tk.StringVar(value="undirected")
        ttk.Radiobutton(control_frame, text="Vô hướng", variable=self.graph_type_var, 
                       value="undirected", command=self.change_graph_type).pack()
        ttk.Radiobutton(control_frame, text="Có hướng", variable=self.graph_type_var, 
                       value="directed", command=self.change_graph_type).pack(pady=5)
        
        # Phân tích
        ttk.Label(control_frame, text="=== PHÂN TÍCH ===", font=('Arial', 10, 'bold')).pack(pady=10)
        
        ttk.Label(control_frame, text="Đỉnh bắt đầu (BFS/DFS):").pack()
        self.start_vertex_entry = ttk.Entry(control_frame)
        self.start_vertex_entry.pack(pady=5)
        
        ttk.Button(control_frame, text="BFS", command=self.perform_bfs).pack(pady=3)
        ttk.Button(control_frame, text="DFS", command=self.perform_dfs).pack(pady=3)
        
        ttk.Label(control_frame, text="Tìm đường đi (từ -> đến):").pack(pady=10)
        self.path_from_entry = ttk.Entry(control_frame)
        self.path_from_entry.pack(pady=3)
        self.path_to_entry = ttk.Entry(control_frame)
        self.path_to_entry.pack(pady=3)
        ttk.Button(control_frame, text="Đường ngắn nhất", command=self.find_shortest_path).pack(pady=5)
        
        ttk.Button(control_frame, text="Kiểm tra 2 phía", command=self.check_bipartite).pack(pady=5)
        # ===== NÂNG CAO (MST) =====
        ttk.Label(control_frame, text="=== NÂNG CAO (MST) ===", font=('Arial', 10, 'bold')).pack(pady=10)
        ttk.Button(control_frame, text="Prim", command=self.run_prim).pack(pady=3)
        ttk.Button(control_frame, text="Kruskal", command=self.run_kruskal).pack(pady=3)

        
        # Chuyển đổi biểu diễn
        ttk.Label(control_frame, text="=== CHUYỂN ĐỔI ===", font=('Arial', 10, 'bold')).pack(pady=10)
        ttk.Button(control_frame, text="→ Ma trận kề", command=self.show_adjacency_matrix).pack(pady=3)
        ttk.Button(control_frame, text="→ Danh sách cạnh", command=self.show_edge_list).pack(pady=3)
        
        # Điều khiển tệp
        ttk.Label(control_frame, text="=== TỆP ===", font=('Arial', 10, 'bold')).pack(pady=10)
        ttk.Button(control_frame, text="Lưu đồ thị", command=self.save_graph).pack(pady=3)
        ttk.Button(control_frame, text="Tải đồ thị", command=self.load_graph).pack(pady=3)
        ttk.Button(control_frame, text="Xóa tất cả", command=self.clear_graph).pack(pady=5)

        
        # ===== PHẦN HIỂN THỊ =====
        self.canvas_frame = ttk.Frame(display_frame)
        self.canvas_frame.pack(fill=tk.BOTH, expand=True)
        
        # Kết quả
        result_frame = ttk.LabelFrame(display_frame, text="Kết quả", padding=5)
        result_frame.pack(fill=tk.X, pady=5)
        
        self.result_text = tk.Text(result_frame, height=8, width=50)
        self.result_text.pack(fill=tk.BOTH, expand=True)
        
        scrollbar = ttk.Scrollbar(result_frame, command=self.result_text.yview)
        scrollbar.pack(side=tk.RIGHT, fill=tk.Y)
        self.result_text.config(yscrollcommand=scrollbar.set)
        
        self.draw_graph()
    
    def add_vertex(self):
        """Thêm đỉnh"""
        vertex = self.vertex_entry.get().strip()
        if vertex:
            self.graph.add_vertex(vertex)
            self.nx_graph.add_node(vertex)
            self.vertex_entry.delete(0, tk.END)
            self.draw_graph()
            self.log_result(f"✓ Thêm đỉnh '{vertex}' thành công")
        else:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập tên đỉnh!")
    
    def add_edge(self):
        """Thêm cạnh"""
        from_v = self.from_vertex_entry.get().strip()
        to_v = self.to_vertex_entry.get().strip()
        
        if not from_v or not to_v:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập cả hai đỉnh!")
            return
        
        try:
            weight = float(self.weight_entry.get())
        except ValueError:
            weight = 1
        
        self.graph.add_edge(from_v, to_v, weight)
        
        if weight == 1:
            self.nx_graph.add_edge(from_v, to_v)
        else:
            self.nx_graph.add_edge(from_v, to_v, weight=weight)
        
        self.from_vertex_entry.delete(0, tk.END)
        self.to_vertex_entry.delete(0, tk.END)
        self.weight_entry.delete(0, tk.END)
        self.weight_entry.insert(0, "1")
        self.draw_graph()
        self.log_result(f"✓ Thêm cạnh '{from_v}' -> '{to_v}' (trọng số: {weight}) thành công")
    
    def change_graph_type(self):
        """Thay đổi loại đồ thị"""
        is_directed = self.graph_type_var.get() == "directed"
        self.graph.is_directed = is_directed
        self.nx_graph = nx.DiGraph() if is_directed else nx.Graph()
        
        for vertex in self.graph.vertices:
            self.nx_graph.add_node(vertex)
        
        for u, v, weight in self.graph.edge_list:
            if weight == 1:
                self.nx_graph.add_edge(u, v)
            else:
                self.nx_graph.add_edge(u, v, weight=weight)
        
        self.draw_graph()
        graph_type_name = "có hướng" if is_directed else "vô hướng"
        self.log_result(f"✓ Đổi thành đồ thị {graph_type_name}")
    
    def perform_bfs(self):
        """Thực hiện BFS"""
        start = self.start_vertex_entry.get().strip()
        if not start:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập đỉnh bắt đầu!")
            return
        
        if start not in self.graph.vertices:
            messagebox.showerror("Lỗi", f"Đỉnh '{start}' không tồn tại!")
            return
        
        result = self.graph.bfs(start)
        result_str = " → ".join(str(v) for v in result)
        self.log_result(f"BFS từ '{start}':\n{result_str}")
    
    def perform_dfs(self):
        """Thực hiện DFS"""
        start = self.start_vertex_entry.get().strip()
        if not start:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập đỉnh bắt đầu!")
            return
        
        if start not in self.graph.vertices:
            messagebox.showerror("Lỗi", f"Đỉnh '{start}' không tồn tại!")
            return
        
        result = self.graph.dfs(start)
        result_str = " → ".join(str(v) for v in result)
        self.log_result(f"DFS từ '{start}':\n{result_str}")
    
    def find_shortest_path(self):
        """Tìm đường đi ngắn nhất"""
        start = self.path_from_entry.get().strip()
        end = self.path_to_entry.get().strip()
        
        if not start or not end:
            messagebox.showwarning("Cảnh báo", "Vui lòng nhập cả hai đỉnh!")
            return
        
        if start not in self.graph.vertices or end not in self.graph.vertices:
            messagebox.showerror("Lỗi", "Một hoặc cả hai đỉnh không tồn tại!")
            return
        
        path = self.graph.shortest_path_bfs(start, end)
        if path:
            path_str = " → ".join(str(v) for v in path)
            self.log_result(f"Đường đi ngắn nhất từ '{start}' đến '{end}':\n{path_str}\nĐộ dài: {len(path)-1} cạnh")
        else:
            self.log_result(f"Không có đường đi từ '{start}' đến '{end}'")
    
    def check_bipartite(self):
        """Kiểm tra đồ thị 2 phía"""
        if not self.graph.vertices:
            messagebox.showinfo("Thông tin", "Đồ thị trống!")
            return
        
        is_bipartite = self.graph.is_bipartite()
        if is_bipartite:
            self.log_result("✓ Đồ thị này LÀ đồ thị 2 phía (Bipartite)")
        else:
            self.log_result("✗ Đồ thị này KHÔNG phải đồ thị 2 phía")
    
    def show_adjacency_matrix(self):
        """Hiển thị ma trận kề"""
        if not self.graph.vertices:
            messagebox.showinfo("Thông tin", "Đồ thị trống!")
            return
        
        matrix, vertices_list = self.graph.to_adjacency_matrix()
        
        result_str = "Ma trận kề:\n\n"
        result_str += "    " + "  ".join(str(v) for v in vertices_list) + "\n"
        for i, v in enumerate(vertices_list):
            result_str += f"{v:3s} " + "  ".join(str(matrix[i][j]) for j in range(len(vertices_list))) + "\n"
        
        self.log_result(result_str)
    
    def show_edge_list(self):
        """Hiển thị danh sách cạnh"""
        if not self.graph.edge_list:
            self.log_result("Danh sách cạnh trống")
            return
        
        result_str = "Danh sách cạnh:\n\n"
        result_str += "Từ  |  Đến  |  Trọng số\n"
        result_str += "------|-------|----------\n"
        for u, v, weight in self.graph.edge_list:
            result_str += f"{str(u):4s} | {str(v):5s} | {weight}\n"
        
        self.log_result(result_str)
    
    def draw_graph(self):
        """Vẽ đồ thị"""
        for widget in self.canvas_frame.winfo_children():
            widget.destroy()
        
        if not self.graph.vertices:
            return
        
        fig = Figure(figsize=(8, 6), dpi=100)
        ax = fig.add_subplot(111)
        
        # Tính toán vị trí nút
        if not self.pos or len(self.pos) != len(self.nx_graph.nodes()):
            self.pos = nx.spring_layout(self.nx_graph, k=2, iterations=50)
        
        # Vẽ nút
        nx.draw_networkx_nodes(self.nx_graph, self.pos, node_color='lightblue', 
                               node_size=800, ax=ax)
        
        # Vẽ cạnh
        nx.draw_networkx_edges(self.nx_graph, self.pos, ax=ax, 
                              arrowsize=20, arrowstyle='->' if self.graph.is_directed else '-',
                              connectionstyle="arc3,rad=0.1")
        
        # Vẽ nhãn
        nx.draw_networkx_labels(self.nx_graph, self.pos, font_size=10, font_weight='bold', ax=ax)
        
        # Vẽ trọng số
        edge_labels = {}
        for u, v, data in self.nx_graph.edges(data=True):
            if 'weight' in data and data['weight'] != 1:
                edge_labels[(u, v)] = data['weight']
        
        if edge_labels:
            nx.draw_networkx_edge_labels(self.nx_graph, self.pos, edge_labels, ax=ax)
        
        ax.axis('off')
        ax.set_title(f"Đồ thị ({'Có hướng' if self.graph.is_directed else 'Vô hướng'})")
        
        canvas = FigureCanvasTkAgg(fig, master=self.canvas_frame)
        canvas.draw()
        canvas.get_tk_widget().pack(fill=tk.BOTH, expand=True)
    
    def log_result(self, message):
        """Ghi kết quả vào khu vực text"""
        self.result_text.config(state=tk.NORMAL)
        self.result_text.delete(1.0, tk.END)
        self.result_text.insert(tk.END, message)
        self.result_text.config(state=tk.DISABLED)
    
    def save_graph(self):
        """Lưu đồ thị"""
        file_path = filedialog.asksaveasfilename(defaultextension=".graph",
                                                 filetypes=[("Graph files", "*.graph"), ("All files", "*.*")])
        if not file_path:
            return
        
        data = {
            'is_directed': self.graph.is_directed,
            'vertices': list(self.graph.vertices),
            'edges': self.graph.edge_list,
            'adjacency_list': dict(self.graph.adjacency_list)
        }
        
        try:
            with open(file_path, 'wb') as f:
                pickle.dump(data, f)
            self.log_result(f"✓ Đồ thị đã được lưu vào:\n{file_path}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể lưu: {str(e)}")
    
    def load_graph(self):
        """Tải đồ thị"""
        file_path = filedialog.askopenfilename(filetypes=[("Graph files", "*.graph"), ("All files", "*.*")])
        if not file_path:
            return
        
        try:
            with open(file_path, 'rb') as f:
                data = pickle.load(f)
            
            self.graph = Graph(is_directed=data['is_directed'])
            self.nx_graph = nx.DiGraph() if data['is_directed'] else nx.Graph()
            
            for edge in data['edges']:
                u, v, weight = edge
                self.graph.add_edge(u, v, weight)
                if weight == 1:
                    self.nx_graph.add_edge(u, v)
                else:
                    self.nx_graph.add_edge(u, v, weight=weight)
            
            self.change_graph_type()
            self.log_result(f"✓ Đồ thị đã được tải từ:\n{file_path}")
        except Exception as e:
            messagebox.showerror("Lỗi", f"Không thể tải: {str(e)}")
    
    def clear_graph(self):
        """Xóa tất cả"""
        if messagebox.askyesno("Xác nhận", "Xóa tất cả đỉnh và cạnh?"):
            self.graph = Graph(is_directed=self.graph.is_directed)
            self.nx_graph = nx.DiGraph() if self.graph.is_directed else nx.Graph()
            self.pos = {}
            self.draw_graph()
            self.log_result("✓ Đồ thị đã được xóa")
    def run_prim(self):
        try:
            mst = self.graph.prim_mst()
            self.highlight_mst(mst, "Prim")
        except ValueError as e:
            messagebox.showerror("Lỗi", str(e))

    def run_kruskal(self):
        try:
            mst = self.graph.kruskal_mst()
            self.highlight_mst(mst, "Kruskal")
        except ValueError as e:
            messagebox.showerror("Lỗi", str(e))

    def highlight_mst(self, mst, name):
        if not mst:
            self.log_result("Không thể tạo MST")
            return

        self.draw_graph()

        fig = plt.gcf()
        ax = plt.gca()

        mst_edges = [(u, v) for u, v, _ in mst]
        nx.draw_networkx_edges(
            self.nx_graph,
            self.pos,
            edgelist=mst_edges,
            edge_color='red',
            width=3,
            ax=ax
        )

        total_weight = sum(w for _, _, w in mst)
        result = f"{name} - Minimum Spanning Tree:\n"
        for u, v, w in mst:
            result += f"{u} - {v} (w={w})\n"
        result += f"Tổng trọng số = {total_weight}"

        self.log_result(result)


def main():
    """Chương trình chính"""
    root = tk.Tk()
    app = GraphApp(root)
    root.mainloop()


if __name__ == "__main__":
    main()
