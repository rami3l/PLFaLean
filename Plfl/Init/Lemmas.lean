module

public section

theorem congr_arg₃
  (f : α → β → γ → δ) {x x' : α} {y y' : β} {z z' : γ}
  (hx : x = x') (hy : y = y') (hz : z = z')
  : f x y z = f x' y' z'
  := by subst hx hy hz; rfl
