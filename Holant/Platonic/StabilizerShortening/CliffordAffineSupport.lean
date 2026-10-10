import Holant.Platonic.StabilizerErasure.QuadraticColumnPhase
import Holant.Platonic.StabilizerLine.Source

/-! Support geometry of a one-dimensional Pauli fixed space. This is a direct
route to affine preservation by arbitrary analytic Clifford normalizers; no
synthesis into the restricted Program syntax is assumed. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching Holant.ReedMuller.CharacterFlat
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerCode
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def diagonalPauli (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) : Pauli n := ⟨0,0,ell⟩

theorem diagonalPauli_delta (ell : BinaryVector n →ₗ[ZMod 2] ZMod 2) :
    (diagonalPauli ell).run delta=delta := by
  ext x
  simp only [diagonalPauli, Pauli.run, phaseRoot_zero, one_mul, add_zero, word_vector]
  by_cases hx : x=origin n
  · subst x; simp [delta]
  · simp [delta,hx]

/-- All literal Z constraints have exactly the one-dimensional delta eigenspace. -/
theorem fixed_diagonal_scalar (v : Signature ℂ n)
    (h : ∀ell,(diagonalPauli ell).run v=v) : ∃c : ℂ,v=c • delta := by
  have hs (w : Word n) (hw : v w≠0) : w=origin n := by
    apply vector_injective
    rw [vector_origin]
    ext i
    have hi := congrFun (h (LinearMap.proj i)) w
    change phaseRoot 0*sign (vectorWord w i)*v (wordVector (vectorWord w+0))=v w at hi
    simp only [phaseRoot_zero,one_mul,add_zero,word_vector] at hi
    rcases binary_cases (vectorWord w i) with hz|hz
    · exact hz
    · exfalso
      apply hw
      rw [hz,sign_one,neg_one_mul] at hi
      linear_combination -hi/2
  refine ⟨v (origin n),?_⟩
  ext w
  by_cases hw : w=origin n
  · subst w; simp [delta]
  · have hv : v w=0 := by by_contra hn; exact hw (hs w hn)
    simp [delta,hw,hv]

/-- Every simultaneous fixer of the complete Pauli stabilizer is on this line. -/
def UniqueFixedLine (f : Signature ℂ n) : Prop :=
  ∀v : Signature ℂ n,(∀P : Pauli n,P.run f=f → P.run v=v) → ∃c : ℂ,v=c • f

theorem clifford_delta_unique (C : AnalyticClifford n) : UniqueFixedLine (C.operator delta) := by
  intro v hv
  have hd : ∀ell,(diagonalPauli ell).run (C.operator.symm v)=C.operator.symm v := by
    intro ell
    obtain ⟨P,hP⟩ := C.pauli_forward (diagonalPauli ell)
    have hp : P.run (C.operator delta)=C.operator delta := by
      rw [←hP,diagonalPauli_delta]
    apply C.operator.injective
    rw [hP,LinearEquiv.apply_symm_apply,hv P hp]
  obtain ⟨c,hc⟩ := fixed_diagonal_scalar (C.operator.symm v) hd
  refine ⟨c,?_⟩
  have hh := congrArg C.operator hc
  simpa using hh

/-- Actual shifts of fixing Paulis form a binary linear subspace. -/
def stabilizerShifts (f : Signature ℂ n) : BinaryCode n where
  carrier := {a | ∃P : Pauli n,P.run f=f ∧ P.shift=a}
  zero_mem' := by
    refine ⟨diagonalPauli 0,?_,rfl⟩
    ext x
    simp [diagonalPauli,Pauli.run]
  add_mem' := by
    rintro a b ⟨P,hP,rfl⟩ ⟨Q,hQ,rfl⟩
    exact ⟨pauliProduct P Q,by rw [pauliProduct_run,hQ,hP],rfl⟩
  smul_mem' := by
    intro a b hb
    rcases binary_cases a with ha|ha
    · subst a
      simp only [zero_smul]
      refine ⟨diagonalPauli 0,?_,rfl⟩
      ext x
      simp [diagonalPauli,Pauli.run]
    · subst a
      simpa only [one_smul] using hb

@[simp] theorem mem_stabilizerShifts (f : Signature ℂ n) (a : BinaryVector n) :
    a∈stabilizerShifts f ↔ ∃P : Pauli n,P.run f=f ∧ P.shift=a := Iff.rfl

theorem shift_support (f : Signature ℂ n) (x : BinaryVector n)
    (hx : f (wordVector x)≠0) (a : BinaryVector n) (ha : a∈stabilizerShifts f) :
    f (wordVector (x+a))≠0 := by
  obtain ⟨P,hP,rfl⟩ := ha
  intro hz
  have he := congrFun hP (wordVector x)
  simp only [Pauli.run,vector_word,hz,mul_zero] at he
  exact hx he.symm

/-- Restriction to one shift orbit commutes with every actual fixing Pauli. -/
theorem restricted_fixed (f : Signature ℂ n) (x₀ : BinaryVector n)
    (P : Pauli n) (hP : P.run f=f) :
    P.run (fun w => if vectorWord w+x₀∈stabilizerShifts f then f w else 0)=
      (fun w => if vectorWord w+x₀∈stabilizerShifts f then f w else 0) := by
  have hp : P.shift∈stabilizerShifts f := ⟨P,hP,rfl⟩
  ext w
  have he : vectorWord w+P.shift+x₀∈stabilizerShifts f ↔
      vectorWord w+x₀∈stabilizerShifts f := by
    constructor
    · intro h
      have hh := (stabilizerShifts f).add_mem h hp
      have hc : vectorWord w+P.shift+x₀+P.shift=vectorWord w+x₀ := by
        calc
          _ = vectorWord w+x₀+(P.shift+P.shift) := by abel
          _ = _ := by rw [binary_self,add_zero]
      simpa only [hc] using hh
    · intro h
      have hh := (stabilizerShifts f).add_mem h hp
      simpa [add_assoc,add_comm,add_left_comm] using hh
  simp only [Pauli.run,vector_word,he]
  split_ifs with hw
  · exact congrFun hP w
  · simp

/-- A nonzero one-dimensional stabilizer state has exactly one affine support coset. -/
theorem unique_fixed_support (f : Signature ℂ n) (hf : UniqueFixedLine f)
    (x₀ : BinaryVector n) (hx₀ : f (wordVector x₀)≠0) (x : BinaryVector n) :
    f (wordVector x)≠0 ↔ x+x₀∈stabilizerShifts f := by
  constructor
  · intro hx
    obtain ⟨c,hc⟩ := hf (fun w => if vectorWord w+x₀∈stabilizerShifts f then f w else 0)
      (fun P hP => restricted_fixed f x₀ P hP)
    have hc1 : c=1 := by
      have hh := congrFun hc (wordVector x₀)
      simp only [vector_word,binary_self,Submodule.zero_mem,ite_true,Pi.smul_apply,smul_eq_mul] at hh
      exact (mul_right_cancel₀ hx₀ (by simpa using hh.symm)).trans rfl
    by_contra hm
    have hh := congrFun hc (wordVector x)
    simp only [vector_word,hm,ite_false,Pi.smul_apply,smul_eq_mul,hc1,one_mul] at hh
    exact hx hh.symm
  · intro hx
    have hh := shift_support f x₀ hx₀ (x+x₀) hx
    have hc : x₀+(x+x₀)=x := by
      calc
        _ = (x₀+x₀)+x := by abel
        _ = x := by rw [binary_self,zero_add]
    simpa only [hc] using hh

end
end Holant.Platonic.StabilizerShortening
