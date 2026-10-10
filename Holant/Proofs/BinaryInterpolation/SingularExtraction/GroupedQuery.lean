import Holant.Proofs.BinaryInterpolation.SingularExtraction.ResidueAnchors


noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.GroupedQuery
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork RawGrouping RawDisjoint ResidueAnchors

variable {K : Type*} [Field K] {s b : ℕ} {arity : ℕ → ℕ}

def table (F : Choice.Table K) (a c : ℕ) (u v : Bool → K) : Choice.Table K :=
  withPower (withPower F a u) c v

def query (F : Choice.Table K) (a c k l : ℕ) (hk : 0 < k) (hl : 0 < l)
    (u v : Bool → K) (r : Input s b arity) : RawClosedNetwork :=
  groupTwo a c k l (augmented (table F a c u v) a c k l hk hl r).val

theorem selected_dvd_of_occurrences (label k : ℕ) (r : Input s b arity)
    (ha : arity label = 1) (hd : k ∣ occurrences label r.val) :
    k ∣ (selected label r.val.vertices).length := by
  rw [selected_length]
  · exact hd
  · intro row hrow he
    have H := (wellFormed_iff_members s b arity r.val).mp r.property
    simpa [he, ha] using (H.1 row hrow).2

theorem query_wellFormed (F : Choice.Table K) (a c k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hab : a ≠ c) (has : a < s) (hcs : c < s)
    (ha : arity a = 1) (hc : arity c = 1) (u v : Bool → K) (r : Input s b arity)
    (h : Live (s:=s) (b:=b) (arity:=arity) (table F a c u v) a c k l hk hl (residue a c k l hk hl r)) :
    (query F a c k l hk hl u v r).WellFormed s b
      (changedArity (changedArity arity a k) c l) := by
  let t := augmented (table F a c u v) a c k l hk hl r
  have hd := augmented_counts (table F a c u v) a c k l hk hl r h
  have hda := selected_dvd_of_occurrences a k t ha hd.1
  have hdc := selected_dvd_of_occurrences c l t hc hd.2
  apply groupOne_wellFormed c l hcs (groupOne a k t.val)
    (groupOne_wellFormed a k has t.val t.property hda)
  rwa [selected_groupOne_other a c k hab]

theorem query_value (F : Choice.Table K) (a c k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hab : a ≠ c)
    (ha : arity a = 1) (hc : arity c = 1) (u v : Bool → K) (r : Input s b arity)
    (h : Live (s:=s) (b:=b) (arity:=arity) (table F a c u v) a c k l hk hl (residue a c k l hk hl r)) :
    Choice.evaluate (table F a c u v) (query F a c k l hk hl u v r).edges.length
      (query F a c k l hk hl u v r).vertices =
      value (table F a c u v) r *
        value (table F a c u v)
          (anchor (table F a c u v) a c k l hk hl (residue a c k l hk hl r) : Input s b arity) := by
  let t := augmented (table F a c u v) a c k l hk hl r
  have hd := augmented_counts (table F a c u v) a c k l hk hl r h
  have hda := selected_dvd_of_occurrences a k t ha hd.1
  have hdc := selected_dvd_of_occurrences c l t hc hd.2
  have he := groupTwo_evaluate F a c k l hab u v t.val hda (by
    rwa [selected_groupOne_other a c k hab])
  exact he.trans (augmented_value (table F a c u v) a c k l hk hl r)

theorem recover (F : Choice.Table K) (a c k l : ℕ)
    (hk : 0 < k) (hl : 0 < l) (hab : a ≠ c)
    (ha : arity a = 1) (hc : arity c = 1) (u v : Bool → K) (r : Input s b arity)
    (h : Live (s:=s) (b:=b) (arity:=arity) (table F a c u v) a c k l hk hl (residue a c k l hk hl r)) :
    Choice.evaluate (table F a c u v) (query F a c k l hk hl u v r).edges.length
        (query F a c k l hk hl u v r).vertices /
      value (table F a c u v)
        (anchor (table F a c u v) a c k l hk hl (residue a c k l hk hl r) : Input s b arity) =
      value (table F a c u v) r := by
  rw [query_value F a c k l hk hl hab ha hc u v r h]
  exact mul_div_cancel_right₀ _ (anchor_nonzero (table F a c u v) a c k l hk hl _ h)

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.GroupedQuery
