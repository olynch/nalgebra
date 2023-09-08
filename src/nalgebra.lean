structure Vector (n : Nat) (α : Type u) where
   data : Array α
   prf : data.size = n

def map {n : Nat} {α β: Type u} (f : α → β) (xs : Vector n α) :=
  Vector.mk (Array.map f xs.data) rfl

theorem zipWithAuxSize {n : Nat} (f : α → β → γ) (as : Array α) (bs : Array β) (ha : as.size = n) (hb : bs.size = n) (j : Nat)
  (hj : j ≤ n) :
  (cs : Array γ) → (hc : cs.size = n - j) → (Array.zipWithAux f as bs (n-j) cs).size = n := by
  induction j with
  | zero =>
    intro cs hc
    rw [Array.zipWithAux]
    simp [ha, hb]
    rw [←Nat.sub_zero n]
    assumption
  | succ k ihk =>
    intro cs hc
    rw [Array.zipWithAux]
    simp [ha, hb]
    have h1 : (Nat.succ k > 0) := Nat.zero_lt_succ k
    have h2 : (n > 0) := Nat.lt_of_lt_of_le h1 hj
    let i := n - Nat.succ k    
    have i_lt_n : i < n := Nat.sub_lt h2 h1    
    simp [i_lt_n]
    have hi : i = n - Nat.succ k := rfl
    simp [←hi]
    have i_in_as : i < as.size := by rw [ha]; assumption
    have i_in_bs : i < bs.size := by rw [hb]; assumption
    let cs' := Array.push cs (f as[i] bs[i])
    have hk : k < n := Nat.lt_of_succ_le hj
    have cs'_size : cs'.size = (i + 1) := by
      simp [Array.push, Array.size]
      assumption
    have hrfds : (i + 1) = n - k := by
      simp [Nat.sub_succ]
      have foo : 0 < (n - k) := Nat.zero_lt_sub_of_lt hk
      simp [Nat.add_one]
      have bar : 0 ≠ (n - k) := Nat.ne_of_lt foo
      simp [Nat.succ_pred (fun (eq : (n - k) = 0) => bar (Eq.symm eq))]
    have ihk0 := ihk (Nat.le_of_lt hk) cs' (Eq.trans cs'_size hrfds)
    simp [hrfds]
    assumption
 
theorem zipWithSizeProof {n : Nat} (f : α → β → γ) (as : Array α) (bs : Array β) (ha : as.size = n) (hb : bs.size = n) :
   (Array.zipWith as bs f).size = n := by
  simp [Array.zipWith]
  have lemma1 := (zipWithAuxSize f as bs ha hb n (Nat.le_refl n) #[] (by simp; simp [Array.size, List.length]))
  rw [Nat.sub_self n] at lemma1
  assumption

def zipWith {n : Nat} {α β γ : Type u} (xs : Vector n α) (ys : Vector n β) (f : α → β → γ) : Vector n γ :=
  let zs₀ := Array.zipWith xs.data ys.data f
  let prf : zs₀.size = n := by
    exact zipWithSizeProof f xs.data ys.data xs.prf ys.prf
  Vector.mk zs₀ prf

def add {n : Nat} {α : Type u} (s : Add α) (xs : Vector n α) (ys : Vector n α) : Vector n α := zipWith xs ys s.add
