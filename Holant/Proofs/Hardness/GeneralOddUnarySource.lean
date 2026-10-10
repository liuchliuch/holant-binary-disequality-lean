import Holant.Proofs.Dichotomy.WithoutIdentity.NoINativeFamily
import Holant.Proofs.Hardness.GeneralOddUnaryOrdinary
import Holant.Proofs.Tetrahedral.ExternalOddCompletion.Loops

/-! An actual original-input consumer of the odd loop descent and unary escape.
The hypotheses are the original finite family, one original nonzero odd row,
and failure of the literal seven-clause predicate.  The new conclusion in the
unary arm is either a nonisotropic unary, two independent original ordinary
unary graphs, or the exact one-sided EO failure.  None is named Hard.
The existing high-odd stopping arm remains explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.GeneralExtraction.NamedContraction
open GeneralOddUnaryOrdinary
namespace Loops
export Holant.LocalDrafts.TetrahedralCompletion.ExternalOddCompletion.Loops
  (selected selected_conservation selected_loop_bound)
end Loops
set_option backward.isDefEq.respectTransparency false

variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
variable (j : Fin s) (ho : Odd (a j.val)) (hnz : G j≠0)


abbrev result := Loops.selected G j ho hnz

def unary (hu : (result G j ho hnz).arity=1) : Network AlgebraicComplex 1 :=
  reboundary ((result G j ho hnz).frame.network G) (finCongr hu)

private theorem cast_signature_eq {m n : ℕ} (h : m=n)
    (f : Signature AlgebraicComplex n) :
    (⟨n,f⟩ : AnySignature AlgebraicComplex)=
      ⟨m,fun x => f (fun i => x (Fin.cast h.symm i))⟩ := by
  cases h
  rfl

theorem unary_uses (hu : (result G j ho hnz).arity=1) :
    Uses (unary G j ho hnz hu) (original G) := by
  intro v
  refine ⟨j,?_⟩
  let D := (result G j ho hnz).frame
  change (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=
    ⟨D.shape.arity v,fun x => G j (fun i => x (Fin.cast (D.labels.vertex_arity v) i))⟩
  exact cast_signature_eq (D.originalArity v) (G j)

theorem unary_ordinary (hu : (result G j ho hnz).arity=1) :
    Ordinary (unary G j ho hnz hu) := fun _ => rfl

theorem unary_nonzero (hu : (result G j ho hnz).arity=1) :
    (unary G j ho hnz hu).denote≠0 := by
  intro hz
  apply (result G j ho hnz).nonzero
  funext x
  have h := congrFun hz (fun i => x ((finCongr hu).symm i))
  simpa only [unary,reboundary_denote,Equiv.symm_apply_apply,Pi.zero_apply] using h

theorem unary_resources (hu : (result G j ho hnz).arity=1) :
    (unary G j ho hnz hu).shape.vertices=1 ∧
    1+2*(unary G j ho hnz hu).shape.edges=a j.val ∧
    (unary G j ho hnz hu).shape.edges≤(a j.val-1)/2 := by
  refine ⟨(result G j ho hnz).frame.one,?_,Loops.selected_loop_bound G j ho hnz⟩
  change 1+2*(result G j ho hnz).frame.shape.edges=a j.val
  rw [←hu]
  exact Loops.selected_conservation G j ho hnz

variable (hu : (result G j ho hnz).arity=1)
variable (hiso : pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote=0)
variable (hside : ¬CommonOneSided (kCoordinates (original G)))

/-- Fixed installation data chosen only after the original-input producer has
proved existence.  No runtime gadget or desired coefficient is supplied. -/
def second : Network AlgebraicComplex 1 :=
  Classical.choose (escape_isotropic (original G) (unary G j ho hnz hu)
    (unary_uses G j ho hnz hu) (unary_ordinary G j ho hnz hu)
    (unary_nonzero G j ho hnz hu) hiso hside)

theorem second_spec : Uses (second G j ho hnz hu hiso hside) (original G) ∧
    Ordinary (second G j ho hnz hu hiso hside) ∧
    pairing (unary G j ho hnz hu).denote (second G j ho hnz hu hiso hside).denote≠0 :=
  Classical.choose_spec (escape_isotropic (original G) (unary G j ho hnz hu)
    (unary_uses G j ho hnz hu) (unary_ordinary G j ho hnz hu)
    (unary_nonzero G j ho hnz hu) hiso hside)

theorem second_independent :
    determinant (unary G j ho hnz hu).denote
      (second G j ho hnz hu hiso hside).denote≠0 :=
  independent_of_isotropic _ _ hiso (second_spec G j ho hnz hu hiso hside).2.2

omit hu hiso hside in

/-- A one-sided result really fails the central EO predicate, since otherwise
the first literal Tract clause would already prove tractability. -/
theorem oneSided_eo_failure (hnot : ¬Tract (original G))
    (hside : CommonOneSided (kCoordinates (preprocess (original G)))) :
    ¬EOTract (centralFamily (kCoordinates (preprocess (original G)))) := by
  intro heo
  apply hnot
  refine ⟨?_,Or.inl ⟨hside,heo⟩⟩
  exact (Set.finite_range _).subset (fun _ h => h.1)

/-- The previously unanalysed unary residual now has this internally produced
three-way classification.  Every graph in the third arm uses original G. -/
theorem unary_cases (hu : (result G j ho hnz).arity=1)
    (hnot : ¬Tract (original G)) :
    pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote≠0 ∨
    (CommonOneSided (kCoordinates (preprocess (original G))) ∧
      ¬EOTract (centralFamily (kCoordinates (preprocess (original G))))) ∨
    (pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote=0 ∧
      ∃ V : Network AlgebraicComplex 1,Uses V (original G) ∧ Ordinary V ∧
        pairing (unary G j ho hnz hu).denote V.denote≠0) := by
  classical
  by_cases hiso : pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote=0
  · by_cases hside : CommonOneSided (kCoordinates (preprocess (original G)))
    · exact .inr (.inl ⟨hside,oneSided_eo_failure G hnot hside⟩)
    · refine .inr (.inr ⟨hiso,?_⟩)
      apply escape_isotropic (original G) (unary G j ho hnz hu)
        (unary_uses G j ho hnz hu) (unary_ordinary G j ho hnz hu)
        (unary_nonzero G j ho hnz hu) hiso
      intro h
      apply hside
      apply h.mono_family
      exact Set.image_mono (fun _ h => h.1)
  · exact .inl hiso

/-- Complete consumption of the actual finite odd descent.  This is a local
producer advance, not the unproved full ordinary odd hardness theorem. -/
theorem source (hnot : ¬Tract (original G)) :
    3≤(result G j ho hnz).arity ∨
    ∃ hu : (result G j ho hnz).arity=1,
      pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote≠0 ∨
      (CommonOneSided (kCoordinates (preprocess (original G))) ∧
        ¬EOTract (centralFamily (kCoordinates (preprocess (original G))))) ∨
      (pairing (unary G j ho hnz hu).denote (unary G j ho hnz hu).denote=0 ∧
        ∃ V : Network AlgebraicComplex 1,Uses V (original G) ∧ Ordinary V ∧
          pairing (unary G j ho hnz hu).denote V.denote≠0) := by
  by_cases hu : (result G j ho hnz).arity=1
  · exact .inr ⟨hu,unary_cases G j ho hnz hu hnot⟩
  · left
    obtain ⟨k,hk⟩ := (result G j ho hnz).odd
    omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralOddUnarySource
