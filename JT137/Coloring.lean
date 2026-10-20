import JT137.Graph

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JT137

def color (v : Vertex) : Fin 4 :=
  if v.val < 4 then 0
  else if v.val < 7 then 1
  else if v.val < 10 then 2
  else 3

abbrev Proper {k : Nat} (arc : Vertex → Vertex → Bool)
    (c : Vertex → Fin k) : Prop :=
  ∀ u v : Vertex, arc u v = true → c u ≠ c v

abbrev Repeats {k : Nat} (c : Vertex → Fin k)
    (u v w x : Vertex) : Prop :=
  c u = c v ∨ c u = c w ∨ c u = c x ∨
  c v = c w ∨ c v = c x ∨ c w = c x

theorem proper36 : Proper arc36 color := by
  decide

theorem proper37 : Proper arc37 color := by
  decide

theorem displayed_no_rainbow36 :
    ∀ u v w x : Vertex,
      arc36 u v = true →
      arc36 v w = true →
      arc36 w x = true →
      Repeats color u v w x := by
  decide

theorem displayed_no_rainbow37 :
    ∀ u v w x : Vertex,
      arc37 u v = true →
      arc37 v w = true →
      arc37 w x = true →
      Repeats color u v w x := by
  decide

end JT137
