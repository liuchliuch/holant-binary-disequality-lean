import Holant.ReedMuller.AffineRadon.ConstantRecognition
import Holant.ReedMuller.AffineRadon.PhysicalBridge

/-! Source Lemma7.19. Affine support and phase are derived from the existing
source class, while every assumed Radon card is its literal quotient value in
a recorded orthogonal frame. The conclusion is the actual flat tensor class. -/
namespace Holant.ReedMuller.AffineRadon
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 theorem source_affine_to_flat_radon {r : ℕ} (hr : 4≤r)
    (f : Signature AlgebraicComplex (2*r)) (hf : Affine f) (hn : f≠0)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) : Flat (fun x => (f x:ℂ)) := by
  obtain ⟨A⟩ := exists_actual_normal_form f hf hn
  exact A.flat_of_radon_cards hr hd

/-- One recorded frame per accessible direction suffices, exactly as in the
source. Flatness is not assumed for every possible coordinate choice. -/
theorem source_affine_to_flat_radon_fixed_frames {r : ℕ} (hr : 4≤r)
    (f : Signature AlgebraicComplex (2*r)) (hf : Affine f) (hn : f≠0)
    (frames : (v : BinaryVector (2*r)) → Accessible v → RadonAccess.RadonFrame (2*r))
    (direction : ∀ v hv,(frames v hv).v=v)
    (cards : ∀ v hv ε,FlatOrZero (fun x =>
      RadonFrame.actualRadon (frames v hv) ε (fun y => (f (wordVector y):ℂ)) (vectorWord x))) :
    Flat (fun x => (f x:ℂ)) := by
  apply source_affine_to_flat_radon hr f hf hn
  intro v hv
  exact ⟨frames v hv,direction v hv,cards v hv⟩

/-- The literal source arity convention, without a chosen half-arity index. -/
theorem source_affine_to_flat_radon_even {n : ℕ} (hn8 : 8≤n) (hnEven : Even n)
    (f : Signature AlgebraicComplex n) (hf : Affine f) (hn : f≠0)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) : Flat (fun x => (f x:ℂ)) := by
  obtain ⟨r,hr⟩ := hnEven
  rw [←two_mul] at hr
  subst n
  exact source_affine_to_flat_radon (by omega) f hf hn hd

/-- Direct consumer of the actual fixed graph/Bell native-X networks from7.22.
All graph and representative scalars are removed by proved identities, not by
an assumed normalization or a freely realized coordinate change. -/
theorem source_affine_to_flat_from_actual_networks {n : ℕ}
    (hn8 : 8≤n+2) (hnEven : Even (n+2))
    (κ : ZMod 2 → ZMod 2 → ℂ) (hκ : ∀ d l,κ d l≠0)
    (f : Signature AlgebraicComplex (n+2)) (hf : Affine f) (hn : f≠0)
    (frames : (v : BinaryVector (n+2)) → Accessible v → RadonAccess.RadonFrame (n+2))
    (direction : ∀ v hv,(frames v hv).v=v)
    (graphs : ∀ v hv,SignedRadon.ActualGraph κ (frames v hv).A)
    (cards : ∀ v hv d,FlatOrZero
      (SignedRadon.signedNetwork (frames v hv) (graphs v hv) (fun x => (f x:ℂ)) d 0).denote) :
    Flat (fun x => (f x:ℂ)) := by
  apply source_affine_to_flat_radon_even hn8 hnEven f hf hn
  intro v hv
  refine ⟨frames v hv,direction v hv,?_⟩
  intro d
  exact RadonFrame.flat_native_network_implies_actualRadon hκ (frames v hv)
    (graphs v hv) (fun x => (f x:ℂ)) d (cards v hv d)

/-- A flat algebraic input has an actual algebraic normalization scalar; the
complex coordinate presentation does not enlarge the source output class. -/
theorem algebraic_flat_witness {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : Flat (fun x => (f x:ℂ))) :
    ∃ (c : AlgebraicComplex) (a : BinaryVector n) (D : BinaryCode n),c≠0 ∧ SelfDual D ∧
      ∀ x,f x=if vectorWord x-a∈D then c else 0 := by
  obtain ⟨c,a,D,hD,he⟩ := hf
  have hz : (fun i => bit (wordVector a i)-a i)=(0:BinaryVector n) := by
    funext i
    change boolEquiv (boolEquiv.symm (a i))-a i=0
    rw [Equiv.apply_symm_apply,sub_self]
  have hc : (f (wordVector a):ℂ)=(c:ℂ) := by
    have H := congrFun he (wordVector a)
    simpa only [flatSignature,hz,Submodule.zero_mem,ite_true] using H
  have hcn : f (wordVector a)≠0 := by
    intro h
    apply c.ne_zero
    rw [←hc,h]
    rfl
  refine ⟨f (wordVector a),a,D,hcn,hD,?_⟩
  intro x
  apply Subtype.ext
  have H := congrFun he x
  change (f x:ℂ)=(if (fun i => bit (x i)-a i)∈D then (c:ℂ) else 0) at H
  rw [H]
  by_cases hx : vectorWord x-a∈D
  · have hx' : (fun i => bit (x i)-a i)∈D := hx
    rw [if_pos hx',if_pos hx]
    exact hc.symm
  · have hx' : (fun i => bit (x i)-a i)∉D := hx
    rw [if_neg hx',if_neg hx]
    rfl

 theorem source_affine_to_flat_radon_algebraic {n : ℕ} (hn8 : 8≤n) (hnEven : Even n)
    (f : Signature AlgebraicComplex n) (hf : Affine f) (hn : f≠0)
    (hd : FlatRadonCards (fun x => (f (wordVector x):ℂ))) :
    ∃ (c : AlgebraicComplex) (a : BinaryVector n) (D : BinaryCode n),c≠0 ∧ SelfDual D ∧
      ∀ x,f x=if vectorWord x-a∈D then c else 0 :=
  algebraic_flat_witness f (source_affine_to_flat_radon_even hn8 hnEven f hf hn hd)

end
end Holant.ReedMuller.AffineRadon
