import Holant.Proofs.Reductions.GeneralExtraction.NativeCopies
import Mathlib.Tactic.Positivity


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.Nonvanishing
open NamedContraction SupportDescent SupportCaps NativeCopies BinaryCarrier
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction

variable {K : Type*} [Field K] {n : ℕ}

def StrictSide (b : Bool) (f : Signature K n) : Prop :=
  ∀ x, f x ≠ 0 → 0 < balance b x

/-- Opposite nonzero charges produce a supported balanced word in a real
disjoint union: l copies of the positive word and k of the negative word. -/
theorem opposite_support_carrier (F : SignatureFamily K) (htwo : (2 : K) ≠ 0)
    (N : Network K n) (hn : 0 < n) (hU : Uses N F) (hN : Native N)
    (x y : Fin n → Bool) (hx : N.denote x ≠ 0) (hy : N.denote y ≠ 0)
    (hk : 0 < balance true x) (hl : balance true y < 0) :
    ∃ C : Network K 0, Uses C F ∧ Native C ∧
      0 < C.shape.vertices ∧ C.denote Fin.elim0 ≠ 0 := by
  let k := (balance true x).toNat
  let l := (-balance true y).toNat
  have hk' : (k : ℤ) = balance true x := Int.toNat_of_nonneg (le_of_lt hk)
  have hl' : (l : ℤ) = -balance true y := Int.toNat_of_nonneg (by omega)
  have hkpos : 0 < k := by omega
  have hlpos : 0 < l := by omega
  let M := (copies N l).tensor (copies N k)
  let z := appendWord (copyWord x l) (copyWord y k)
  have hz : M.denote z ≠ 0 := by
    rw [tensor_word, copies_word, copies_word]
    exact mul_ne_zero (pow_ne_zero l hx) (pow_ne_zero k hy)
  have hb : balance true z = 0 := by
    rw [balance_append, balance_copy, balance_copy, hk', hl']
    ring
  apply balanced_carrier F htwo (by simp only [copyArity_eq]; positivity) M
    (tensor_uses F _ _ (copies_uses F N hU l) (copies_uses F N hU k))
    (tensor_native _ _ (copies_native N hN l) (copies_native N hN k)) z hz hb

/-- This is the general supported-word dichotomy used by extraction. The
zero signature is excluded automatically by the two negated side predicates. -/
theorem carrier_of_not_strict (htwo : (2 : K) ≠ 0) (hn : 0 < n)
    (f : Signature K n) (hfalse : ¬ StrictSide false f) (htrue : ¬ StrictSide true f) :
    ∃ C : Network K 0, Uses C {⟨n, f⟩} ∧ Native C ∧
      0 < C.shape.vertices ∧ C.denote Fin.elim0 ≠ 0 := by
  obtain ⟨x, hx, hxb⟩ : ∃ x, f x ≠ 0 ∧ balance true x ≤ 0 := by
    simpa only [StrictSide, not_forall, not_imp, not_lt, exists_prop] using htrue
  obtain ⟨y, hy, hyb⟩ : ∃ y, f y ≠ 0 ∧ balance false y ≤ 0 := by
    simpa only [StrictSide, not_forall, not_imp, not_lt, exists_prop] using hfalse
  have hypos : 0 ≤ balance true y := by
    have he := balance_negate true y
    simp only [Bool.not_true] at he
    omega
  by_cases hxzero : balance true x = 0
  · exact balanced_carrier {⟨n, f⟩} htwo hn (Network.corolla f)
      (fun _ => Set.mem_singleton _) (fun e => Fin.elim0 e) x (by simpa using hx) hxzero
  by_cases hyzero : balance true y = 0
  · exact balanced_carrier {⟨n, f⟩} htwo hn (Network.corolla f)
      (fun _ => Set.mem_singleton _) (fun e => Fin.elim0 e) y (by simpa using hy) hyzero
  exact opposite_support_carrier {⟨n, f⟩} htwo (Network.corolla f) hn
    (fun _ => Set.mem_singleton _) (fun e => Fin.elim0 e) y x
    (by simpa using hy) (by simpa using hx) (by omega) (by omega)

end Holant.LocalDrafts.Hardness.GeneralExtraction.Nonvanishing
