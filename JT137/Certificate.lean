import JT137.Counterexample

namespace JT137

def IsCounterexample (arc : Vertex → Vertex → Bool) : Prop :=
  (∀ u : Vertex, arc u u = false) ∧
  (∀ u v : Vertex, arc u v = true → arc v u = false) ∧
  (∃ c : Vertex → Fin 4, Proper arc c) ∧
  (∀ c : Vertex → Fin 3, ¬ Proper arc c) ∧
  (∀ c : Vertex → Fin 4, Proper arc c →
    ∀ u v w x : Vertex,
      arc u v = true →
      arc v w = true →
      arc w x = true →
      Repeats c u v w x)

theorem counterexample36 : IsCounterexample arc36 := by
  exact ⟨loopless36, oriented36, ⟨color, proper36⟩,
    no_three_coloring36, no_rainbow36⟩

theorem counterexample37 : IsCounterexample arc37 := by
  exact ⟨loopless37, oriented37, ⟨color, proper37⟩,
    no_three_coloring37, no_rainbow37⟩

end JT137
