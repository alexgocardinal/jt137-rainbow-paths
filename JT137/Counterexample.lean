import JT137.Uniqueness

set_option maxRecDepth 100000
set_option maxHeartbeats 0

namespace JT137

def representative (v : Vertex) : Vertex :=
  if v.val < 4 then 0
  else if v.val < 7 then 4
  else if v.val < 10 then 7
  else 10

theorem representative_agrees :
    ∀ u v : Vertex,
      color u = color v →
      representative u = representative v := by
  decide

theorem vertex_cases :
    ∀ v : Vertex,
      v = 0 ∨ v = 1 ∨ v = 2 ∨ v = 3 ∨
      v = 4 ∨ v = 5 ∨ v = 6 ∨ v = 7 ∨
      v = 8 ∨ v = 9 ∨ v = 10 ∨ v = 11 ∨ v = 12 := by
  decide

theorem canonical36 (c : Vertex → Fin 4)
    (h : Proper arc36 c) (v : Vertex) :
    c v = c (representative v) := by
  rcases forced_partition36 c h with
    ⟨same0, same1, same2, same3, same4,
     same5, same6, same7, same8⟩
  rcases vertex_cases v with
    hv | hv | hv | hv | hv | hv | hv |
    hv | hv | hv | hv | hv | hv
  · subst v
    change c 0 = c 0
    rfl
  · subst v
    change c 1 = c 0
    exact same0
  · subst v
    change c 2 = c 0
    exact same1
  · subst v
    change c 3 = c 0
    exact same2
  · subst v
    change c 4 = c 4
    rfl
  · subst v
    change c 5 = c 4
    exact same3
  · subst v
    change c 6 = c 4
    exact same4
  · subst v
    change c 7 = c 7
    rfl
  · subst v
    change c 8 = c 7
    exact same5
  · subst v
    change c 9 = c 7
    exact same6
  · subst v
    change c 10 = c 10
    rfl
  · subst v
    change c 11 = c 10
    exact same7
  · subst v
    change c 12 = c 10
    exact same8

theorem same_class36 (c : Vertex → Fin 4)
    (h : Proper arc36 c) (u v : Vertex)
    (huv : color u = color v) : c u = c v := by
  calc
    c u = c (representative u) := canonical36 c h u
    _ = c (representative v) :=
      congrArg c (representative_agrees u v huv)
    _ = c v := (canonical36 c h v).symm

theorem no_rainbow36 (c : Vertex → Fin 4)
    (h : Proper arc36 c) :
    ∀ u v w x : Vertex,
      arc36 u v = true →
      arc36 v w = true →
      arc36 w x = true →
      Repeats c u v w x := by
  intro u v w x huv hvw hwx
  rcases displayed_no_rainbow36 u v w x huv hvw hwx with
    he | he | he | he | he | he
  · exact Or.inl (same_class36 c h u v he)
  · exact Or.inr (Or.inl (same_class36 c h u w he))
  · exact Or.inr (Or.inr (Or.inl (same_class36 c h u x he)))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inl (same_class36 c h v w he))))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (same_class36 c h v x he)))))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (same_class36 c h w x he)))))

theorem no_rainbow37 (c : Vertex → Fin 4)
    (h : Proper arc37 c) :
    ∀ u v w x : Vertex,
      arc37 u v = true →
      arc37 v w = true →
      arc37 w x = true →
      Repeats c u v w x := by
  have h36 : Proper arc36 c := by
    intro u v huv
    exact h u v (arc36_implies37 u v huv)
  intro u v w x huv hvw hwx
  rcases displayed_no_rainbow37 u v w x huv hvw hwx with
    he | he | he | he | he | he
  · exact Or.inl (same_class36 c h36 u v he)
  · exact Or.inr (Or.inl (same_class36 c h36 u w he))
  · exact Or.inr (Or.inr (Or.inl (same_class36 c h36 u x he)))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inl (same_class36 c h36 v w he))))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inl (same_class36 c h36 v x he)))))
  · exact Or.inr (Or.inr (Or.inr
      (Or.inr (Or.inr (same_class36 c h36 w x he)))))

end JT137
