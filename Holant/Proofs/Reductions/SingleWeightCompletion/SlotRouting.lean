import Holant.Proofs.Reductions.SingleWeightCompletion.ChargeProgram
import Mathlib.Algebra.BigOperators.Fin


noncomputable section
namespace Holant.LocalDrafts.Hardness.SingleWeightCompletion.SlotRouting
open scoped BigOperators
variable {V : ℕ} (k : Fin V → ℕ) (bit : Fin V → Bool) (color : Fin V → Fin V)
def mass (c : Fin V) (b : Bool) (v : Fin V) : ℕ := if color v=c ∧ bit v=b then k v else 0
def size (c : Fin V) (b : Bool) : ℕ := ∑ v, mass k bit color c b v
abbrev Slot := Σ v : Fin V, Fin (k v)
abbrev Edge := Σ c : Fin V, Fin (size k bit color c false)
def total : ℕ := ∑ c, size k bit color c false
def Balanced : Prop := ∀ c, size k bit color c false = size k bit color c true

theorem mass_le (c : Fin V) (b : Bool) (v : Fin V) : mass k bit color c b v ≤ k v := by
  by_cases h : color v=c ∧ bit v=b <;> simp [mass,h]
theorem mass_positive (c : Fin V) (b : Bool) (v : Fin V) (h : 0 < mass k bit color c b v) :
    color v=c ∧ bit v=b := by
  by_contra hh
  simp [mass,hh] at h
def index (p : Slot k) : Fin (size k bit color (color p.1) (bit p.1)) :=
  finSigmaFinEquiv ⟨p.1,⟨p.2.val,by simpa [mass] using p.2.isLt⟩⟩
def decode (c : Fin V) (b : Bool) (i : Fin (size k bit color c b)) : Slot k :=
  let p := finSigmaFinEquiv.symm i
  ⟨p.1,⟨p.2.val,lt_of_lt_of_le p.2.isLt (mass_le k bit color c b p.1)⟩⟩
theorem decode_color (c : Fin V) (b : Bool) (i : Fin (size k bit color c b)) :
    color (decode k bit color c b i).1=c :=
  (mass_positive k bit color c b _ (Nat.zero_lt_of_lt (finSigmaFinEquiv.symm i).2.isLt)).1
theorem decode_bit (c : Fin V) (b : Bool) (i : Fin (size k bit color c b)) :
    bit (decode k bit color c b i).1=b :=
  (mass_positive k bit color c b _ (Nat.zero_lt_of_lt (finSigmaFinEquiv.symm i).2.isLt)).2
theorem decode_index (p : Slot k) :
    decode k bit color (color p.1) (bit p.1) (index k bit color p) = p := by
  let e : (Σ v : Fin V, Fin (mass k bit color (color p.1) (bit p.1) v)) ≃
      Fin (size k bit color (color p.1) (bit p.1)) := finSigmaFinEquiv
  let q : Σ v : Fin V, Fin (mass k bit color (color p.1) (bit p.1) v) :=
    ⟨p.1,⟨p.2.val,by simpa [mass] using p.2.isLt⟩⟩
  let forget : (Σ v : Fin V, Fin (mass k bit color (color p.1) (bit p.1) v)) → Slot k :=
    fun t => ⟨t.1,⟨t.2.val,lt_of_lt_of_le t.2.isLt
      (mass_le k bit color (color p.1) (bit p.1) t.1)⟩⟩
  change forget (e.symm (e q)) = p
  rw [e.symm_apply_apply]

section BalancedRouting
variable (h : Balanced k bit color)
include h
theorem size_eq (c : Fin V) (b : Bool) : size k bit color c b = size k bit color c false := by
  cases b
  · rfl
  · exact (h c).symm
def route (p : Slot k) : Edge k bit color × Bool :=
  (⟨color p.1,Fin.cast (size_eq k bit color h _ _) (index k bit color p)⟩,bit p.1)
def unroute (q : Edge k bit color × Bool) : Slot k :=
  decode k bit color q.1.1 q.2 (Fin.cast (size_eq k bit color h _ _).symm q.1.2)
theorem unroute_route (p : Slot k) : unroute k bit color h (route k bit color h p) = p := by
  let hs := size_eq k bit color h (color p.1) (bit p.1)
  change decode k bit color (color p.1) (bit p.1)
    (Fin.cast hs.symm (Fin.cast hs (index k bit color p))) = p
  have he : Fin.cast hs.symm (Fin.cast hs (index k bit color p)) = index k bit color p :=
    Fin.ext rfl
  rw [he]
  exact decode_index k bit color p
set_option backward.isDefEq.respectTransparency false in
theorem route_unroute (q : Edge k bit color × Bool) : route k bit color h (unroute k bit color h q) = q := by
  obtain ⟨⟨c,i⟩,b⟩ := q
  let j : Fin (size k bit color c b) := Fin.cast (size_eq k bit color h c b).symm i
  have hc := decode_color k bit color c b j
  have hb := decode_bit k bit color c b j
  apply Prod.ext
  · apply Sigma.ext hc
    apply (Fin.heq_ext_iff (congrArg (fun c => size k bit color c false) hc)).mpr
    change (index k bit color (decode k bit color c b j)).val = i.val
    simp only [index,finSigmaFinEquiv_apply]
    change (∑ v : Fin (decode k bit color c b j).1.val,
      mass k bit color (color (decode k bit color c b j).1)
        (bit (decode k bit color c b j).1)
        (Fin.castLE (decode k bit color c b j).1.isLt.le v)) +
      (decode k bit color c b j).2.val = i.val
    rw [hc,hb]
    have he := congrArg Fin.val
      ((@finSigmaFinEquiv V (mass k bit color c b)).apply_symm_apply j)
    simpa only [decode,finSigmaFinEquiv_apply,Fin.val_cast,j] using! he
  · exact hb
def equiv : Slot k ≃ Edge k bit color × Bool where
  toFun := route k bit color h
  invFun := unroute k bit color h
  left_inv := unroute_route k bit color h
  right_inv := route_unroute k bit color h
def numbered : Slot k ≃ Fin (total k bit color) × Bool :=
  (equiv k bit color h).trans (Equiv.prodCongr finSigmaFinEquiv (Equiv.refl Bool))

theorem same_component (e : Fin (total k bit color)) :
    color ((numbered k bit color h).symm (e,false)).1 =
      color ((numbered k bit color h).symm (e,true)).1 := by
  exact (decode_color k bit color _ _ _).trans (decode_color k bit color _ _ _).symm
theorem prescribed_bit (e : Fin (total k bit color)) (b : Bool) :
    bit ((numbered k bit color h).symm (e,b)).1 = b := decode_bit k bit color _ _ _
theorem route_side (p : Slot k) : (numbered k bit color h p).2=bit p.1 := rfl

/-- Exact global edge numbering, not merely a cardinality bound. -/
theorem route_index (p : Slot k) : (numbered k bit color h p).1.val =
    (∑ c : Fin (color p.1).val, size k bit color (Fin.castLE (color p.1).isLt.le c) false) +
      (∑ v : Fin p.1.val, mass k bit color (color p.1) (bit p.1) (Fin.castLE p.1.isLt.le v)) + p.2.val := by
  change (finSigmaFinEquiv (route k bit color h p).1).val = _
  rw [finSigmaFinEquiv_apply]
  change (∑ c : Fin (color p.1).val,
    size k bit color (Fin.castLE (color p.1).isLt.le c) false) +
      (index k bit color p).val = _
  rw [index,finSigmaFinEquiv_apply]
  simp only [Nat.add_assoc]

end BalancedRouting
end Holant.LocalDrafts.Hardness.SingleWeightCompletion.SlotRouting
