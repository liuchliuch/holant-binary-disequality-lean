import Holant.Proofs.Hardness.GeneralOddHighTerminalGcd

/-! Actual positive-charge reservoirs for the signed divisibility residue.
A finite disjoint union shifts a negative supported charge into the positive
half-line. Every original coefficient and every internal edge is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueCharge
open Holant
open Holant.LocalDrafts.Hardness.GeneralExtraction
open NamedContraction SupportDescent SupportCaps NativeCopies
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
set_option backward.isDefEq.respectTransparency false

variable {K : Type*} [Field K] {m l : ℕ}

/-- The number of copies is a positive integer, chosen directly from the
negative charge. No inverse occurrence or arbitrary tensor factor is used. -/
theorem positive_shift (F : SignatureFamily K) (b : Bool)
    (P : Network K m) (Q : Network K l)
    (hPF : Uses P F) (hPX : Native P) (hQF : Uses Q F) (hQX : Native Q)
    (x : Fin m → Bool) (y : Fin l → Bool)
    (hx : P.denote x≠0) (hy : Q.denote y≠0)
    (q r : ℕ) (hq : 0<q) (hpx : balance b x=q) (hqy : balance b y=-(r : ℤ)) :
    ∃ t : ℕ,0<t ∧ (t : ℤ)=(r+1)*q-r ∧
      ∃ N : Network K (copyArity m (r+1)+l),Uses N F ∧ Native N ∧
        ∃ w : Fin (copyArity m (r+1)+l) → Bool,
          N.denote w≠0 ∧ balance b w=t ∧
          N.shape.vertices=(r+1)*P.shape.vertices+Q.shape.vertices ∧
          N.shape.edges=(r+1)*P.shape.edges+Q.shape.edges := by
  let N := (copies P (r+1)).tensor Q
  let w := appendWord (copyWord x (r+1)) y
  have hpos : (0 : ℤ)<(r+1)*q-r := by
    have hq' : (1 : ℤ)≤q := by omega
    have hr : (0 : ℤ)≤r := by positivity
    nlinarith
  let t := ((r+1)*(q : ℤ)-r).toNat
  have ht : (t : ℤ)=(r+1)*q-r := Int.toNat_of_nonneg (le_of_lt hpos)
  refine ⟨t,by omega,ht,N,
    tensor_uses F _ _ (copies_uses F P hPF (r+1)) hQF,
    tensor_native _ _ (copies_native P hPX (r+1)) hQX,w,?_,?_,?_,?_⟩
  · change ((copies P (r+1)).tensor Q).denote (appendWord (copyWord x (r+1)) y)≠0
    rw [tensor_word,copies_word]
    exact mul_ne_zero (pow_ne_zero _ hx) hy
  · simp only [w,balance_append,balance_copy,hpx,hqy,ht]
    push_cast
    ring
  · simp only [N,Network.tensor_vertices,copies_vertices]
  · simp only [N,Network.tensor_edges,GeneralOddHighTerminalCharge.copies_edges]

/-- Divisibility of the reservoir charge and its shifted positive charge
forces divisibility of the original negative charge. -/
theorem negative_dvd_of_shift {n q r t : ℕ} (hq : n∣q) (ht : n∣t)
    (he : (t : ℤ)=(r+1)*q-r) : n∣r := by
  have hq' : (n : ℤ)∣(q : ℤ) := by exact_mod_cast hq
  have ht' : (n : ℤ)∣(t : ℤ) := by exact_mod_cast ht
  have hmul : (n : ℤ)∣((r : ℤ)+1)*q := dvd_mul_of_dvd_right hq' _
  have hdiff : (n : ℤ)∣(((r : ℤ)+1)*q-t) := dvd_sub hmul ht'
  have hh : ((r : ℤ)+1)*q-t=r := by linarith
  rw [hh] at hdiff
  exact_mod_cast hdiff

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddResidueCharge
