import Std

namespace JT137

abbrev Vertex := Fin 13


def arcs36 : List (Vertex × Vertex) :=
  [(0, 4), (0, 6), (0, 8), (0, 9), (0, 12), (1, 10), (3, 6), (3, 7), (3, 10), (3, 12), (4, 1), (4, 2), (4, 8), (4, 10), (4, 12), (5, 1), (5, 9), (5, 12), (7, 1), (7, 2), (7, 6), (7, 10), (7, 12), (8, 2), (8, 6), (9, 6), (9, 10), (11, 1), (11, 2), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (12, 1), (12, 2)]

def arc36 (u v : Vertex) : Bool :=
  arcs36.contains (u, v)

theorem arc_count36 : arcs36.length = 36 := by
  decide

theorem loopless36 :
    ∀ u : Vertex, arc36 u u = false := by
  decide

theorem oriented36 :
    ∀ u v : Vertex,
      arc36 u v = true → arc36 v u = false := by
  decide

def arcs37 : List (Vertex × Vertex) :=
  [(0, 4), (0, 6), (0, 8), (0, 9), (0, 12), (1, 10), (3, 4), (3, 6), (3, 7), (3, 10), (3, 12), (4, 1), (4, 2), (4, 8), (4, 10), (4, 12), (5, 1), (5, 9), (5, 12), (7, 1), (7, 2), (7, 6), (7, 10), (7, 12), (8, 2), (8, 6), (9, 6), (9, 10), (11, 1), (11, 2), (11, 5), (11, 6), (11, 7), (11, 8), (11, 9), (12, 1), (12, 2)]

def arc37 (u v : Vertex) : Bool :=
  arcs37.contains (u, v)

theorem arc_count37 : arcs37.length = 37 := by
  decide

theorem loopless37 :
    ∀ u : Vertex, arc37 u u = false := by
  decide

theorem oriented37 :
    ∀ u v : Vertex,
      arc37 u v = true → arc37 v u = false := by
  decide

end JT137
