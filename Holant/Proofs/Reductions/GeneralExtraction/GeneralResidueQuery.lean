import Holant.Proofs.Reductions.GeneralExtraction.RawFactorGrouping
import Holant.Proofs.BinaryInterpolation.SingularExtraction.ResidueMachine
import Holant.Complexity.FixedGadgetSubstitution.Size


noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
namespace Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralResidueQuery
open Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
open RawFactorGrouping
variable {K : Type} [Field K] {s : ℕ} {arity : ℕ → ℕ}
variable (F : Choice.Table K) (a k : ℕ) (hk : 0 < k) (f : Signature K (arity a))

abbrev Source := ResidueAnchors.Input s 1 arity
abbrev targetArity := RawGrouping.changedArity arity a (k * arity a)
abbrev Target := ResidueAnchors.Input s 1 (targetArity (arity:=arity) a k)
abbrev source := sourceTable F a f
abbrev target := targetTable F a k f

def IsLive (r : Source (s:=s) (arity:=arity)) : Prop :=
  ResidueAnchors.Live (s:=s) (b:=1) (arity:=arity) (source F a f) a a k 1 hk (by omega)
    (ResidueAnchors.residue a a k 1 hk (by omega) r)

abbrev augmented (r : Source (s:=s) (arity:=arity)) :=
  ResidueAnchors.augmented (source F a f) a a k 1 hk (by omega) r

def scale (r : Source (s:=s) (arity:=arity)) : K :=
  ResidueAnchors.value (source F a f)
    (ResidueAnchors.anchor (source F a f) a a k 1 hk (by omega)
      (ResidueAnchors.residue a a k 1 hk (by omega) r) : Source (s:=s) (arity:=arity))

theorem scale_nonzero (r : Source (s:=s) (arity:=arity)) (h : IsLive F a k hk f r) :
    scale F a k hk f r ≠ 0 :=
  ResidueAnchors.anchor_nonzero (source F a f) a a k 1 hk (by omega) _ h

theorem divisible (r : Source (s:=s) (arity:=arity)) (h : IsLive F a k hk f r) :
    k ∣ (selectedRows a (augmented F a k hk f r).val.vertices).length := by
  have hd := (ResidueAnchors.augmented_counts (source F a f) a a k 1 hk (by omega) r h).1
  simpa only [occurrences, selectedRows] using hd

def query (ha : a < s) (r : Source (s:=s) (arity:=arity)) (h : IsLive F a k hk f r) :
    Target (s:=s) (arity:=arity) a k :=
  ⟨group a k (augmented F a k hk f r).val,
    group_wellFormed a k ha _ (augmented F a k hk f r).property (divisible F a k hk f r h)⟩

theorem query_roundtrip (ha : a < s) (r : Source (s:=s) (arity:=arity))
    (h : IsLive F a k hk f r) :
    (RawClosedNetwork.validatedEncoding s 1 (targetArity (arity:=arity) a k)).decode
      ((RawClosedNetwork.validatedEncoding s 1 (targetArity (arity:=arity) a k)).encode
        (query F a k hk f ha r h)) = some (query F a k hk f ha r h) :=
  (RawClosedNetwork.validatedEncoding _ _ _).decode_encode _

theorem query_value (ha : a < s) (r : Source (s:=s) (arity:=arity))
    (h : IsLive F a k hk f r) :
    ResidueAnchors.value (target F a k f) (query F a k hk f ha r h) =
      ResidueAnchors.value (source F a f) r * scale F a k hk f r := by
  have H := (RawGrouping.wellFormed_iff_members _ _ _ _).mp
    (augmented F a k hk f r).property
  have hv := group_value F a k f (augmented F a k hk f r).val
    (divisible F a k hk f r h) (by
      intro row hrow he
      simpa [he] using (H.1 row hrow).2)
  exact hv.trans (ResidueAnchors.augmented_value (source F a f) a a k 1 hk (by omega) r)

theorem recover (ha : a < s) (r : Source (s:=s) (arity:=arity))
    (h : IsLive F a k hk f r) :
    ResidueAnchors.value (target F a k f) (query F a k hk f ha r h) /
      scale F a k hk f r = ResidueAnchors.value (source F a f) r := by
  rw [query_value]
  exact mul_div_cancel_right₀ _ (scale_nonzero F a k hk f r h)

/-- Each branch contains literal validated query records and a fixed
residue-dependent scalar. This data type makes no runtime-cost claim. -/
inductive QueryPlan (B K : Type)
  | zero : QueryPlan B K
  | one : B → K → QueryPlan B K

def QueryPlan.run {B K : Type} [Mul K] [Zero K] (value : B → K) : QueryPlan B K → K
  | .zero => 0
  | .one q c => value q * c

def plan (ha : a < s) (r : Source (s:=s) (arity:=arity)) :
    QueryPlan (Target (s:=s) (arity:=arity) a k) K :=
  if h : IsLive F a k hk f r then .one (query F a k hk f ha r h) (scale F a k hk f r)⁻¹
  else .zero

/-- Total semantics on every valid source input. No caller provides an
oracle equation: run is instantiated with the actual target Holant sum. -/
theorem plan_correct (ha : a < s) (r : Source (s:=s) (arity:=arity)) :
    (plan F a k hk f ha r).run (ResidueAnchors.value (target F a k f)) =
      ResidueAnchors.value (source F a f) r := by
  by_cases h : IsLive F a k hk f r
  · simpa only [plan, dif_pos h, QueryPlan.run, ← div_eq_mul_inv] using
      recover F a k hk f ha r h
  · simp only [plan, dif_neg h, QueryPlan.run]
    exact (ResidueAnchors.dead_value (source F a f) a a k 1 hk (by omega) r h).symm

/-- Both sides are ordinary decoded native-X graphs, including all edge
endpoint checks. This explicitly connects Choice to the existing decoder. -/
theorem decoded_recover (ha : a < s) (r : Source (s:=s) (arity:=arity))
    (h : IsLive F a k hk f r) :
    ((query F a k hk f ha r h).val.realize (query F a k hk f ha r h).property
      (Tables.typed (target F a k f) s (targetArity (arity:=arity) a k))
      (fun _ => Signature.disequality)).denote Fin.elim0 / scale F a k hk f r =
    (r.val.realize r.property (Tables.typed (source F a f) s arity)
      (fun _ => Signature.disequality)).denote Fin.elim0 := by
  rw [Tables.denote_eq_evaluate, Tables.denote_eq_evaluate]
  exact recover F a k hk f ha r h

def anchorBound : ℕ := ResidueAnchors.anchorSize (s:=s) (b:=1) (arity:=arity)
  (source F a f) a a k 1 hk (by omega)

theorem query_size (ha : a < s) (r : Source (s:=s) (arity:=arity))
    (h : IsLive F a k hk f r) :
    (query F a k hk f ha r h).val.vertices.length + (query F a k hk f ha r h).val.edges.length ≤
      (RawClosedNetwork.encoding.encode r.val).length + anchorBound (s:=s) F a k hk f := by
  have hg := group_vertex_bound a k (augmented F a k hk f r).val
  have hs := ResidueAnchors.augmented_size (source F a f) a a k 1 hk (by omega) r
  change (group a k (augmented F a k hk f r).val).vertices.length +
    (augmented F a k hk f r).val.edges.length ≤ _
  exact (Nat.add_le_add_right hg _).trans hs

/-- Bound stated directly on original bytes. Only size is asserted here;
the time proof must compile the grouping operation, not evaluate Holant. -/
theorem query_encoding_length (ha : a < s) (A : ℕ)
    (hA : ∀ i < s, targetArity (arity:=arity) a k i ≤ A)
    (r : Source (s:=s) (arity:=arity)) (h : IsLive F a k hk f r) :
    let z := (RawClosedNetwork.encoding.encode r.val).length + anchorBound (s:=s) F a k hk f
    (RawClosedNetwork.encoding.encode (query F a k hk f ha r h).val).length ≤
      2 * ((2 * (2*s+2+(4*z+6)*A)+2)*z+1)+1+(4*z+1) := by
  intro z
  have hb := raw_length_le _ (query F a k hk f ha r h).property A hA
  have hs := query_size F a k hk f ha r h
  have hv : (query F a k hk f ha r h).val.vertices.length ≤ z := by dsimp [z]; omega
  have he : (query F a k hk f ha r h).val.edges.length ≤ z := by dsimp [z]; omega
  apply hb.trans
  have hm := Nat.mul_le_mul_right A (Nat.add_le_add_right (Nat.mul_le_mul_left 4 he) 6)
  have ht := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hm (2*s+2))) 2) hv
  have hE := Nat.mul_le_mul_left 4 he
  norm_num at ⊢
  omega

/-- The existing actual finite scanner already handles general arity: only
the label counts are inspected. Its second modulus is the harmless 1. -/
def anchorScanner := ResidueMachine.anchorComputes (s:=s) (b:=1) (arity:=arity)
  k hk (source F a f) a a 1 (by omega)

end Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralResidueQuery
