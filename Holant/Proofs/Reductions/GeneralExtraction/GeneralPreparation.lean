import Holant.Proofs.Reductions.GeneralExtraction.GroupingCompiler
import Holant.Proofs.Reductions.GeneralExtraction.GeneralResidueQuery
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Preparation


noncomputable section
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPreparation
open Holant.Complexity Computability BinaryCompose FixedFieldMachines
open Holant.Complexity.UniversalPairReduction.Surgery
open FixedGadgetSubstitution RawClosedNetwork
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
variable {K : Type} [Field K] {s b : ℕ} {arity : ℕ → ℕ}
variable (F : Choice.Table K) (a k : ℕ) (hk : 0 < k) (ha : a < s)

abbrev balanced := Preparation.balanced (s:=s) (b:=b) (arity:=arity) F a a k 1 hk (by omega)

def grouped (r : ResidueAnchors.Input s b arity) :
    ResidueAnchors.Input s b (RawGrouping.changedArity arity a (k*arity a)) :=
  let t := balanced F a k hk r
  ⟨RawFactorGrouping.group a k t.val, RawFactorGrouping.group_wellFormed a k ha t.val t.property (by
    have h := (Preparation.balanced_counts F a a k 1 hk (by omega) r).1
    exact h)⟩

/-- The first closed preprocessing chain for a general n-ary factor.
Output validation is retyping identical bytes, not a hidden repair program. -/
def computes : Computes (validatedEncoding s b arity)
    (validatedEncoding s b (RawGrouping.changedArity arity a (k*arity a)))
    (grouped F a k hk ha) :=
  recode ((Preparation.balancedComputes F a a k 1 hk (by omega)).andThen
    (GroupingCompiler.computes s b arity a k hk)) id (fun _ => rfl) (fun _ => rfl)

theorem grouped_live (r : ResidueAnchors.Input s b arity)
    (h : ResidueAnchors.Live (s:=s) (b:=b) (arity:=arity) F a a k 1 hk (by omega)
      (ResidueAnchors.residue a a k 1 hk (by omega) r)) :
    (grouped F a k hk ha r).val =
      RawFactorGrouping.group a k (ResidueAnchors.augmented F a a k 1 hk (by omega) r).val := by
  simp only [grouped, balanced, Preparation.balanced_live F a a k 1 hk (by omega) r h]

theorem grouped_dead (r : ResidueAnchors.Input s b arity)
    (h : ¬ ResidueAnchors.Live (s:=s) (b:=b) (arity:=arity) F a a k 1 hk (by omega)
      (ResidueAnchors.residue a a k 1 hk (by omega) r)) :
    (grouped F a k hk ha r).val = ⟨[], []⟩ := by
  simp [grouped, balanced, Preparation.balanced_dead F a a k 1 hk (by omega) r h,
    ResidueAnchors.empty, RawFactorGrouping.group, RawFactorGrouping.selectedRows,
    RawFactorGrouping.packs, RawGrouping.keep]

theorem primitive_bound (r : ResidueAnchors.Input s b arity) :
    primitiveCost (computes (s:=s) (b:=b) (arity:=arity) F a k hk ha).machine ((computes (s:=s) (b:=b) (arity:=arity) F a k hk ha).outputs r).steps
      (some (Turing.initList (computes (s:=s) (b:=b) (arity:=arity) F a k hk ha).machine.computer
        ((validatedEncoding s b arity).encode r))) ≤
      (primitivePolynomial (computes (s:=s) (b:=b) (arity:=arity) F a k hk ha)).eval ((validatedEncoding s b arity).encode r).length :=
  computes_primitive_cost (computes (s:=s) (b:=b) (arity:=arity) F a k hk ha) r

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralPreparation
