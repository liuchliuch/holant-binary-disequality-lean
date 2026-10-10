import Holant.Proofs.Hardness.GeneralEOARSNonclosedCoefficients
import Holant.Proofs.Hardness.GeneralEOARSNonclosedMass
import Holant.Proofs.Hardness.GeneralEOARSNonclosedCriterion
import Holant.Proofs.Hardness.GeneralEOCentralHoleCoordinates

/-! The finite support consequence of a saturated mating at a selected pair
of ports, and the exact fixed-weight covariance calculation in that order. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedPrefix
open Holant Holant.Tractable
open scoped BigOperators
namespace C
export GeneralEOARSNonclosedCoefficients (row complementary_mass diagonal_norm cross_norm)
end C
namespace G
export GeneralEOARSNonclosedGram (rowMass rowInner saturated_support)
end G
namespace O
export GeneralEOPinnedDescentOperations (word)
end O
namespace T
export GeneralEOCentralHoleCoordinates (tail2 word_tail)
end T
namespace M
export GeneralEOARSNonclosedMating (output network denote)
end M
namespace V
export GeneralEOARSNonclosedMass (correlation mass spin)
end V
namespace S
export GeneralEOARSNonclosedSupport (toggle FreePair)
end S
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

abbrev inclusion : AlgebraicComplex →+* ℂ := (algebraicClosure ℚ ℂ).subtype
def complex (f : Signature AlgebraicComplex n) : Signature ℂ n := fun x => inclusion (f x)

@[simp] theorem complex_zero (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    complex f x=0 ↔ f x=0 := by simp [complex]

theorem output_map (f : Signature AlgebraicComplex (n+2)) (x : Fin 4 → Bool) :
    inclusion (M.output f x)=M.output (complex f) x := by
  simp only [M.output,map_sum,map_mul,complex]

theorem sum_prefix {K : Type*} [AddCommMonoid K] (F : (Fin (n+2) → Bool) → K) :
    (∑x,F x)=(∑z,F (O.word false false z))+(∑z,F (O.word false true z))+
      (∑z,F (O.word true false z))+(∑z,F (O.word true true z)) := by
  classical
  have step {m : ℕ} (H : (Fin (m+1) → Bool) → K) :
      (∑x,H x)=∑b : Bool,∑z : Fin m → Bool,H (Fin.cons b z) := by
    let : Fintype (Bool × (Fin m → Bool)) := @instFintypeProd _ _ Bool.fintype inferInstance
    rw [←(Fin.consEquiv (fun _ : Fin (m+1) => Bool)).sum_comp,Fintype.sum_prod_type]
    rfl
  rw [step]
  simp_rw [step]
  simp only [Fintype.sum_bool,O.word]
  ac_rfl

theorem correlation_prefix (f : Signature ℂ (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale f) :
    V.correlation (V.mass f) 0 1=
      2*(G.rowMass (C.row f false false)-G.rowMass (C.row f false true)) := by
  have hh : V.correlation (V.mass f) 0 1 =
      G.rowMass (C.row f false false)-G.rowMass (C.row f false true)-
      G.rowMass (C.row f true false)+G.rowMass (C.row f true true) := by
    rw [V.correlation,sum_prefix]
    simp [V.mass,V.spin,O.word,C.row,G.rowMass,Finset.sum_neg_distrib]
    ring
  have h00 := C.complementary_mass f hf false false
  have h01 := C.complementary_mass f hf false true
  simp only [Bool.not_false,Bool.not_true] at h00 h01
  rw [hh,h00,h01]
  ring

theorem row_zero (u : (Fin n → Bool) → ℂ) (h : G.rowMass u=0) : ∀ z,u z=0 := by
  have hz := (Finset.sum_eq_zero_iff_of_nonneg (fun z (_ : z∈Finset.univ) => sq_nonneg ‖u z‖)).mp h
  intro z
  exact norm_eq_zero.mp (sq_eq_zero_iff.mp (hz z (Finset.mem_univ z)))

theorem toggle_word (a b : Bool) (z : Fin n → Bool) :
    S.toggle 0 1 (O.word a b z)=O.word (!a) (!b) z := by
  funext k
  refine Fin.cases ?_ (fun k => Fin.cases ?_ (fun k => ?_) k) k
  · simp [S.toggle,O.word]
  · simp [S.toggle,O.word]
  · have h0 : k.succ.succ ≠ (0 : Fin (n+2)) := by exact Fin.succ_ne_zero _
    have h1 : k.succ.succ ≠ (1 : Fin (n+2)) := by
      intro h
      have := congrArg Fin.val h
      simp at this
    simp [S.toggle,O.word,h0,h1]

theorem free_prefix (f : Signature AlgebraicComplex (n+2))
    (hf : GeneralEOARSBoundary.ARSUpToScale (complex f))
    (hz : G.rowMass (C.row (complex f) false false)=0)
    (hb : 0<G.rowMass (C.row (complex f) false true))
    (sat : ‖G.rowInner (C.row (complex f) false true) (C.row (complex f) true false)‖=
      G.rowMass (C.row (complex f) false true)) : S.FreePair f 0 1 := by
  have h00 := row_zero _ hz
  have h11 := row_zero (C.row (complex f) true true)
    ((C.complementary_mass (complex f) hf false false).trans hz)
  have fibers := G.saturated_support (C.row (complex f) false true)
    (C.row (complex f) true false) _ hb rfl
    (C.complementary_mass (complex f) hf false true) sat
  have opposite (x : Fin (n+2) → Bool) (hx : f x≠0) : x 0≠x 1 := by
    have hs : complex f (O.word (x 0) (x 1) (T.tail2 x))≠0 := by
      rw [T.word_tail]
      simpa using hx
    cases h0 : x 0 <;> cases h1 : x 1 <;> simp only [h0,h1] at hs ⊢
    · exact False.elim (hs (h00 _))
    · decide
    · decide
    · exact False.elim (hs (h11 _))
  refine ⟨by intro h; have hv := congrArg Fin.val h; norm_num at hv,opposite,?_⟩
  intro x hx
  have ho := opposite x hx
  have hs : complex f (O.word (x 0) (x 1) (T.tail2 x))≠0 := by
    rw [T.word_tail]
    simpa using hx
  rw [← T.word_tail x,toggle_word]
  apply (complex_zero f _).not.mp
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp only [h0,h1,Bool.not_false,Bool.not_true] at hs ho ⊢
  · exact False.elim (ho rfl)
  · exact (fibers _).mp hs
  · exact (fibers _).mpr hs
  · exact False.elim (ho rfl)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOARSNonclosedPrefix
