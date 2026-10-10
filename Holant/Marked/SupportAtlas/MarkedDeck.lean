import Holant.Marked.SupportAtlas.CardTransport
import Holant.Marked.Reversal
import Holant.Projective.CyclicPhasePencil.Algebraic

/-! Source-sector and fixed-representative bridge to the weighted complete deck.
Every normalization below is proved from the original physical contraction. -/
noncomputable section
namespace Holant.Marked.SupportAtlas
open Holant.Tractable Holant.Projective

abbrev Phase (m : ℕ) := {t : Scalar // Roots m t}

def nonstandard {m : ℕ} (P : Parameters m) : Prop := match P with
  | .M _ => False
  | .B _ => True
  | .A _ _ _ _ _ _ _ => True

def delta {m : ℕ} (P : Parameters m) : Scalar := match P with
  | .M _ => 1
  | .B _ => 1
  | .A _ _ eta _ _ _ _ => -eta⁻¹

theorem marked_range {m : ℕ} (P : Parameters m) : 3 ≤ m := by cases P <;> omega

theorem delta_ne_zero {m : ℕ} (P : Parameters m) : delta P ≠ 0 := by
  cases P with
  | M => exact one_ne_zero
  | B => exact one_ne_zero
  | A hm he eta s hr hn hs =>
    exact neg_ne_zero.mpr (inv_ne_zero (hr.ne_zero (by omega)))

theorem delta_root {m : ℕ} (P : Parameters m) : Roots m ((delta P)^2) := by
  cases P with
  | M => simp [delta, Roots]
  | B => simp [delta, Roots]
  | A hm he eta s hr hn hs => simpa [delta] using hr.inverse_square

theorem marked_edge {m : ℕ} (P : Parameters m) (hP : nonstandard P) :
    sectorEdge P.basis = scale P.edgeMultiplier (diagonalKernel 1 (delta P)) := by
  rw [P.edge_exact]
  cases P with
  | M => exact hP.elim
  | B => congr 1; funext a b; cases a <;> cases b <;> rfl
  | A => rfl

def complexMatrix (M : Mat) : CMat := fun a b => (M a b : ℂ)
def complexTensor (q : Signature Scalar 4) : Signature ℂ 4 := fun x => (q x : ℂ)

@[simp] theorem complexMatrix_scale (c : Scalar) (M : Mat) :
    complexMatrix (scale c M) = (c : ℂ) • complexMatrix M := by funext a b; simp [complexMatrix, scale]
@[simp] theorem complexMatrix_mul (M N : Mat) :
    complexMatrix (Kernel.mul M N) = Kernel.mul (complexMatrix M) (complexMatrix N) := by
  funext a b; simp [complexMatrix, Kernel.mul_apply]
@[simp] theorem complexMatrix_diagonal (d : Scalar) :
    complexMatrix (diagonalKernel 1 d) = diagonalC (d : ℂ) := by
  funext a b; cases a <;> cases b <;> simp [complexMatrix, diagonalKernel, diagonalC]
@[simp] theorem complexMatrix_zero : complexMatrix (0 : Mat) = 0 := rfl

theorem groupM_complex_root {m : ℕ} (hm : 0 < m) (M : Mat) (h : M ∈ groupM m) :
    IsRootMonomial m (complexMatrix M) := by
  obtain ⟨t,ht,⟨c,hc,rfl⟩ | ⟨c,hc,rfl⟩⟩ := h
  all_goals
    have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
    have htC : (t : ℂ) ≠ 0 := by exact_mod_cast ht.ne_zero hm
    have htR : (t : ℂ)^m = 1 := by exact_mod_cast ht
    rw [complexMatrix_scale]
    apply (rootMonomial_smul_iff m _ hcC _).mpr
  · left
    simp [IsRootMonomial, complexMatrix, R, diagonalKernel, htC, htR]
  · right
    simp [complexMatrix, S, R, diagonalKernel, Kernel.mul_apply, Signature.disequality,
      htC, div_pow, htR]

theorem safeWeighted_smul_iff (m : ℕ) (d c : ℂ) (hc : c ≠ 0) (M : CMat) :
    SafeWeighted m d (c • M) ↔ SafeWeighted m d M := by
  have he : Kernel.mul (c • M) (diagonalC d) = c • Kernel.mul M (diagonalC d) := by
    funext a b; simp [Kernel.mul_apply]; ring
  simp only [SafeWeighted, he, rootMonomial_smul_iff m c hc, smul_eq_zero, hc, false_or]

theorem safeWeighted_of_physical {m : ℕ} (P : Parameters m) (hP : nonstandard P)
    (B : Mat) (hB : B = 0 ∨ sectorTransfer P.basis B ∈ groupM m) :
    SafeWeighted m (delta P : ℂ) (complexMatrix (transport P.basis B)) := by
  rcases hB with rfl | hB
  · left; funext a b; simp [complexMatrix, transport, Kernel.mul_apply]
  · right
    have hh := groupM_complex_root P.positive _ hB
    rw [← transport_mul_edge, marked_edge P hP, scale_mul_right,
      complexMatrix_scale, complexMatrix_mul, complexMatrix_diagonal] at hh
    exact (rootMonomial_smul_iff m (P.edgeMultiplier : ℂ)
      (by exact_mod_cast P.edgeMultiplier_ne_zero) _).mp hh

/-- Fixed actual binary representatives from the source's complete marked group deck. -/
structure Representatives (F : SignatureFamily Scalar) (m : ℕ) (U : InvertibleKernel) where
  matrix : Bool → Phase m → Mat
  multiplier : Bool → Phase m → Scalar
  multiplier_ne_zero : ∀ p t, multiplier p t ≠ 0
  actual : ∀ p t, Gadget.Realizes F .disequality (kernelSignature (matrix p t))
  transfer : ∀ p t, sectorTransfer U (matrix p t) =
    scale (multiplier p t) (if p then S t.val else R t.val)

/-- Literal actual card hypotheses: every ordered physical output is zero or current-group safe. -/
def PhysicalDeck {m : ℕ} (F : SignatureFamily Scalar) (P : Parameters m)
    (q : Signature Scalar 4) (reps : Representatives F m P.basis) : Prop :=
  ∀ (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m),
    physicalCard q e (reps.matrix p t) = 0 ∨
      sectorTransfer P.basis (physicalCard q e (reps.matrix p t)) ∈ groupM m

/-- The deck's current-group condition is exactly the original marked transfer condition. -/
theorem current_group_iff {m : ℕ} (P : Parameters m) (B : Mat) :
    sectorTransfer P.basis B ∈ groupM m ↔ Kernel.mul B Signature.disequality ∈ P.group := by
  simpa only [sectorTransfer, conjugate_inverse'] using P.conjugates_group (sectorTransfer P.basis B)

theorem contract0_scale (q : Signature Scalar 4) (E : Mat) (c : Scalar) :
    contract0 q (scale c E) = scale c (contract0 q E) := by
  funext u v; simp [contract0, scale]; ring

/-- The exact recorded normalization of every actual card, before any analytic quotient. -/
theorem physical_card_normalization {m : ℕ} (F : SignatureFamily Scalar)
    (P : Parameters m) (hP : nonstandard P) (q : Signature Scalar 4)
    (reps : Representatives F m P.basis) (e : Equiv.Perm (Fin 4)) (p : Bool) (t : Phase m) :
    transport P.basis (physicalCard q e (reps.matrix p t)) =
      scale (P.edgeMultiplier * reps.multiplier p t)
        (contract0 (reorder (P.basis.symm.action q) e)
          (Kernel.mul (diagonalKernel 1 (delta P)) (if p then S t.val else R t.val))) := by
  rw [physicalCard_transport, Kernel.mul_assoc, transport_mul_edge, reps.transfer,
    marked_edge P hP, scale_mul, contract0_scale]

theorem join_eq_permute (e : Equiv.Perm (Fin 4)) (a b u v : Bool) :
    join e a b u v = permuteWord e ![a,b,u,v] := rfl

/-- The transported finite sum is exactly the source's E/O weighted pencil. -/
theorem complex_weighted_card (q : Signature Scalar 4) (e : Equiv.Perm (Fin 4))
    (d t : Scalar) (p : Bool) :
    complexMatrix (contract0 (reorder q e)
      (Kernel.mul (diagonalKernel 1 d) (if p then S t else R t))) =
      weightedCard (d : ℂ) (complexTensor q) e p (t : ℂ) := by
  funext u v
  cases p <;> simp [complexMatrix, complexTensor, contract0, reorder, permuteWord,
    weightedCard, effectiveKernel, diagonalC, diagonalKernel, Kernel.mul_apply,
    R, S, Signature.disequality, join_eq_permute]

/-- The complete sampled pencil hypothesis follows from actual physical outputs,
with their fixed representative multipliers cancelled only analytically. -/
theorem safeDeck_of_physical {m : ℕ} (F : SignatureFamily Scalar)
    (P : Parameters m) (hP : nonstandard P) (q : Signature Scalar 4)
    (reps : Representatives F m P.basis) (h : PhysicalDeck F P q reps) :
    SafeDeck m (delta P : ℂ) (complexTensor (P.basis.symm.action q)) := by
  intro e p t ht
  let z : Phase m := ⟨CyclicPhasePencil.algebraicRoot P.positive t ht,
    CyclicPhasePencil.algebraicRoot_pow P.positive t ht⟩
  have hh := safeWeighted_of_physical P hP _ (h e p z)
  rw [physical_card_normalization F P hP q reps, complexMatrix_scale, complex_weighted_card] at hh
  exact (safeWeighted_smul_iff m (delta P : ℂ)
    (↑(P.edgeMultiplier * reps.multiplier p z) : ℂ)
    (by exact_mod_cast mul_ne_zero P.edgeMultiplier_ne_zero (reps.multiplier_ne_zero p z)) _).mp hh

end Holant.Marked.SupportAtlas
