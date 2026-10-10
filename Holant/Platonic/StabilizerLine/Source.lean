import Holant.Platonic.StabilizerLine.Normalization
import Holant.Platonic.StabilizerLine.StandardPauli
import Holant.Platonic.StabilizerLine.LiteralAffine

/-! Source Lemma 9.18, with the necessary explicit amplitude normalization.
A genuine unitary Clifford acts on both original tensors. Only afterward is
its nonzero amplitude divided out; this common scalar leaves support unchanged. -/
namespace Holant.Platonic.StabilizerLine
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
open scoped ComplexConjugate
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def Nonproportional (u v : Signature ℂ n) : Prop :=
  ¬∃ c : ℂ,v=fun x => c*u x

/-- Constructed normalization by a genuine unitary Pauli normalizer. -/
theorem exists_clifford_normalization (u : Signature ℂ n) (hu : ComplexAffine u) (hun : u≠0) :
    ∃ (C : AnalyticClifford n) (α : ℂ),α≠0 ∧
      C.operator u=(fun x => α*delta x) ∧
      (∀ f,ComplexAffine f → ComplexAffine (C.operator f)) ∧
      (∀ f,ComplexAffine f → ComplexAffine (C.operator.symm f)) := by
  obtain ⟨P,α,hα,he⟩ := exists_normalizing_program u hu hun
  exact ⟨P.clifford,α,hα,he,P.affine,P.inverse.affine⟩

/-- Full sharp stabilizer-line statement. Both operators act on the original
u and v, the scale is nonzero, and the support classification is derived from
the original three affine hypotheses without added support assumptions. -/
theorem source_sharp_stabilizer_line (u v : Signature ℂ n)
    (hu : ComplexAffine u) (hun : u≠0) (hv : ComplexAffine v) (hvn : v≠0)
    (hnp : Nonproportional u v) (c : ℂ) (hc : c≠0)
    (hw : ComplexAffine (fun x => u x+c*v x)) (hwn : (fun x => u x+c*v x)≠0) :
    ∃ (C : AnalyticClifford n) (α : ℂ),α≠0 ∧
      C.operator u=(fun x => α*delta x) ∧
      (fun x => α⁻¹*C.operator u x)=delta ∧
      ComplexAffine (C.operator v) ∧ C.operator v≠0 ∧
      Nonproportional (C.operator u) (C.operator v) ∧ SharpSupport (C.operator v) := by
  obtain ⟨P,α,hα,he,hs⟩ := program_sharp_line u v hu hun hv hvn c hc hw hwn
  refine ⟨P.clifford,α,hα,he,?_,P.affine v hv,P.nonzero v hvn,?_,hs⟩
  · funext x
    rw [Program.clifford_apply,he]
    dsimp
    rw [←mul_assoc,inv_mul_cancel₀ hα,one_mul]
  · rintro ⟨a,ha⟩
    apply hnp
    refine ⟨a,P.injective ?_⟩
    have hl := P.linear u 0 a 0
    simp only [zero_mul,add_zero] at hl
    exact ha.trans hl.symm

/-- Direct specialization to the existing exact algebraic-complex Affine
predicate. Arbitrary complex c is retained in the third tensor hypothesis. -/
theorem source_algebraic_stabilizer_line (u v : Signature AlgebraicComplex n)
    (hu : Affine u) (hv : Affine v)
    (hun : (fun x => (u x:ℂ))≠0) (hvn : (fun x => (v x:ℂ))≠0)
    (hnp : Nonproportional (fun x => (u x:ℂ)) (fun x => (v x:ℂ)))
    (c : ℂ) (hc : c≠0)
    (hw : ComplexAffine (fun x => (u x:ℂ)+c*(v x:ℂ)))
    (hwn : (fun x => (u x:ℂ)+c*(v x:ℂ))≠0) :
    ∃ (C : AnalyticClifford n) (α : ℂ),α≠0 ∧
      C.operator (fun x => (u x:ℂ))=(fun x => α*delta x) ∧
      SharpSupport (C.operator (fun x => (v x:ℂ))) := by
  obtain ⟨C,α,hα,he,_,_,_,_,hs⟩ := source_sharp_stabilizer_line _ _
    (complexAffine_of_affine hu) hun (complexAffine_of_affine hv) hvn hnp c hc hw hwn
  exact ⟨C,α,hα,he,hs⟩

theorem hermitian_scaled_delta (c d : ℂ) :
    hermitian (fun x : Word n => c*delta x) (fun x => d*delta x)=conj c*d := by
  simp [hermitian,delta,apply_ite,ite_mul,mul_ite]

/-- The amplitude clarification is necessary even for the one-port input
2δ: no genuine unitary Clifford can send it exactly to the unit delta. -/
theorem no_clifford_sends_two_delta_to_delta (C : AnalyticClifford n) :
    C.operator (fun x => (2:ℂ)*delta x)≠delta := by
  intro he
  have h := C.unitary (fun x => (2:ℂ)*delta x) (fun x => (2:ℂ)*delta x)
  rw [he] at h
  have hd : hermitian (delta : Signature ℂ n) delta=1 := by
    simpa using (hermitian_scaled_delta (n:=n) 1 1)
  rw [hd,hermitian_scaled_delta] at h
  have h2 : conj (2:ℂ)=2 := map_ofNat _ _
  rw [h2] at h
  norm_num at h

end
end Holant.Platonic.StabilizerLine
