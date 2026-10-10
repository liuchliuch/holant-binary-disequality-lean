import Holant.Platonic.StabilizerErasure.Encoder

/-! Exact scalar-versus-logical-Pauli alternatives for a concrete encoder. -/
namespace Holant.Platonic.StabilizerErasure
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n k a : ℕ}

def IsScalar {m : ℕ} (T : Signature ℂ m → Signature ℂ m) : Prop :=
  ∃c : ℂ,∀f,T f=c • f

theorem pauli_scalar_value (P : Pauli k) (c : ℂ)
    (h : ∀f,P.run f=c • f) : c=phaseRoot P.phase := by
  have he := congrFun (h (fun _ => 1)) (origin k)
  simpa [Pauli.run] using he.symm

theorem pauli_scalar_iff (P : Pauli k) :
    IsScalar P.run ↔ P.shift=0 ∧ P.character=0 := by
  constructor
  · rintro ⟨c,h⟩
    have hc := pauli_scalar_value P c h
    subst c
    have hh (x : BinaryVector k) : P.character x=0 := by
      have he := congrFun (h (fun _ => 1)) (wordVector x)
      simp only [Pauli.run,vector_word,mul_one,Pi.smul_apply,smul_eq_mul] at he
      have hs : sign (P.character x)=1 := by
        apply mul_left_cancel₀ (phaseRoot_ne_zero P.phase)
        simpa using he
      rcases binary_cases (P.character x) with hz|ho
      · exact hz
      · rw [ho,sign_one] at hs;norm_num at hs
    have hz : P.shift=0 := by
      have he := congrFun (h delta) (origin k)
      simp only [Pauli.run,vector_origin,map_zero,sign_zero,mul_one,zero_add,
        Pi.smul_apply,smul_eq_mul,delta,ite_true] at he
      by_contra hn
      have hw : wordVector P.shift≠origin k := by
        intro hw
        apply hn
        simpa using congrArg vectorWord hw
      simp [hw] at he
      exact phaseRoot_ne_zero P.phase he.symm
    exact ⟨hz,LinearMap.ext hh⟩
  · rintro ⟨hs,hc⟩
    refine ⟨phaseRoot P.phase,?_⟩
    intro f
    ext w
    simp [Pauli.run,hs,hc]

/-- If the conjugated Pauli has no ancilla X label, it preserves the code
and acts there as the explicit logical Pauli. -/
theorem pauli_attachZero
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a)
    (P : Pauli n) (h : (e P.shift).2=0) (f : Signature ℂ k) :
    P.run (attachZero e f)=attachZero e ((logicalPauli e P).run f) := by
  ext w
  obtain ⟨⟨u,v⟩,rfl⟩ := (wordBlockEquiv e).symm.surjective w
  simp only [Pauli.run,attachZero,LinearMap.coe_mk,AddHom.coe_mk,wordBlockEquiv,
    Equiv.coe_fn_symm_mk,vector_word,map_add,LinearEquiv.apply_symm_apply,
    Prod.fst_add,Prod.snd_add,h,add_zero,word_vector]
  by_cases hv : vectorWord v=0
  · simp only [hv,ite_true]
    rfl
  · simp [hv]

/-- Extend a logical Pauli by identity on all initialized coordinates. -/
def extendLogicalPauli
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) (Q : Pauli k) : Pauli n where
  phase := Q.phase
  shift := e.symm (Q.shift,0)
  character := Q.character.comp (leftCoordinates e)

theorem logicalPauli_extend
    (e : BinaryVector n ≃ₗ[ZMod 2] BinaryVector k × BinaryVector a) (Q : Pauli k) :
    logicalPauli e (extendLogicalPauli e Q)=Q := by
  cases Q
  simp only [logicalPauli,extendLogicalPauli,LinearEquiv.apply_symm_apply]
  congr 1
  ext x
  simp [StabilizerLine.firstCharacter,leftCoordinates]

/-- Every logical Pauli has an exact physical Pauli representative.  This
establishes the logical-Pauli part of the source's stabilizer-isometry
definition for our arbitrary invertible binary coordinate splitting. -/
theorem StabilizerIsometry.logical_representatives (V : StabilizerIsometry k n)
    (Q : Pauli k) : ∃P : Pauli n,∀f,P.run (V.map f)=V.map (Q.run f) := by
  obtain ⟨P,hP⟩ := V.clifford.pauli_forward (extendLogicalPauli V.coordinates Q)
  refine ⟨P,?_⟩
  intro f
  change P.run (V.clifford.operator (attachZero V.coordinates f))=
    V.clifford.operator (attachZero V.coordinates (Q.run f))
  rw [←hP,pauli_attachZero _ _ (by simp [extendLogicalPauli]),logicalPauli_extend]

/-- The nonzero branch is an actual invariant-code action, not merely an
equality of compressed matrix entries. -/
theorem StabilizerIsometry.pauli_compression_or_lift
    (V : StabilizerIsometry k n) (P : Pauli n) :
    (∀f,V.adjoint (P.run (V.map f))=0) ∨
      ∃Q : Pauli k,∀f,P.run (V.map f)=V.map (Q.run f) := by
  obtain ⟨Q,hQ⟩ := V.clifford.inverse_conjugates P
  by_cases h : (V.coordinates Q.shift).2=0
  · right
    refine ⟨logicalPauli V.coordinates Q,?_⟩
    intro f
    apply V.clifford.operator.symm.injective
    change V.clifford.operator.symm
      (P.run (V.clifford.operator (attachZero V.coordinates f)))=
      V.clifford.operator.symm (V.clifford.operator _)
    rw [hQ,LinearEquiv.symm_apply_apply,pauli_attachZero _ _ h]
  · left
    intro f
    change evaluateZero V.coordinates
      (V.clifford.operator.symm (P.run (V.clifford.operator (attachZero V.coordinates f))))=_
    rw [hQ,evaluateZero_pauli_attachZero,if_neg h]

theorem StabilizerIsometry.nonscalar_pauli_lift (V : StabilizerIsometry k n)
    (P : Pauli n) (h : ¬IsScalar (fun f => V.adjoint (P.run (V.map f)))) :
    ∃Q : Pauli k,(Q.shift≠0 ∨ Q.character≠0) ∧
      ∀f,P.run (V.map f)=V.map (Q.run f) := by
  rcases V.pauli_compression_or_lift P with hz|⟨Q,hQ⟩
  · exact (h ⟨0,fun f => by simp [hz]⟩).elim
  · refine ⟨Q,?_,hQ⟩
    by_contra hn
    have hzero : Q.shift=0 ∧ Q.character=0 := by simpa using hn
    obtain ⟨c,hc⟩ := (pauli_scalar_iff Q).mpr hzero
    apply h
    refine ⟨c,?_⟩
    intro f
    change V.adjoint (P.run (V.map f))=c • f
    rw [hQ,V.adjoint_map,hc]

/-- A correctable Hermitian Pauli (expressed by its involution law) has
expectation 0, +1, or -1.  The proof uses the actual invariant-code lift. -/
theorem StabilizerIsometry.scalar_involution_values (V : StabilizerIsometry k n)
    (P : Pauli n) (hP : ∀f,P.run (P.run f)=f) (c : ℂ)
    (hc : ∀f,V.adjoint (P.run (V.map f))=c • f) : c=0 ∨ c=1 ∨ c= -1 := by
  rcases V.pauli_compression_or_lift P with hz|⟨Q,hQ⟩
  · left
    have he := congrFun (hc (fun _ => 1)) (origin k)
    simpa [hz] using he.symm
  · have hscalar (f : Signature ℂ k) : Q.run f=c • f := by
      simpa [hQ] using hc f
    have htwice (f : Signature ℂ k) : Q.run (Q.run f)=f := by
      apply V.injective
      rw [←hQ,←hQ,hP]
    have he := congrFun (htwice (fun _ => 1)) (origin k)
    rw [hscalar,hscalar] at he
    have hs : c*c=1 := by simpa using he
    have hz : (c-1)*(c+1)=0 := by linear_combination hs
    rcases mul_eq_zero.mp hz with h|h
    · exact Or.inr (Or.inl (sub_eq_zero.mp h))
    · exact Or.inr (Or.inr (by linear_combination h))

end
end Holant.Platonic.StabilizerErasure
