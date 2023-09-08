structure Vector (n : Nat) (α : Type u) where
   data : Array α
   prf : data.size = n

def map {n : Nat} {α β: Type u} (f : α → β) (xs : Vector n α) :=
  Vector.mk (Array.map f xs.data) rfl

theorem zipWithSizeProof {α β γ : Type u} (xs : Array α) (ys : Array β) (f : α → β → γ) : (Array.zipWith xs ys f).size = xs.size := by
  induction xs.data with
  | nil => simp [Array.zipWith]; simp [Array.zipWithAux]; _
  | cons x rest ih => _

def zipWith {n : Nat} {α β γ : Type u} (xs : Vector n α) (ys : Vector n β) (f : α → β → γ) : Vector n γ :=
  let zs₀ := Array.zipWith xs.data ys.data f
  let prf : zs₀.size = n := by
    simp [zipWithSizeProof xs.data ys.data f]
    simp [xs.prf]
  Vector.mk zs₀ prf
