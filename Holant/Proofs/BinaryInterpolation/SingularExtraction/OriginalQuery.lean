import Holant.Proofs.BinaryInterpolation.SingularExtraction.SourcePowers
import Holant.Proofs.BinaryInterpolation.SingularExtraction.Tables
import Holant.Complexity.FixedGadgetSubstitution.Partition
import Holant.Complexity.FixedGadgetSubstitution.Identity


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.OriginalQuery
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork ResidueAnchors

variable {K : Type} [Field K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
variable (U : PowerMacro G u) (V : PowerMacro G v)
set_option backward.isDefEq.respectTransparency false

def templates (i : ℕ) : Template :=
  if i = s then U.labels.template else if i = s+1 then V.labels.template else identityTemplate arity i

theorem templates_valid : ∀ i < s+2, (templates G u v U V i).WellFormed s 1 arity := by
  intro i hi
  by_cases ha : i = s
  · simpa [templates, ha] using U.labels.wellFormed
  by_cases hb : i = s+1
  · simpa [templates, ha, hb] using V.labels.wellFormed
  · have h : i < s := by omega
    simpa [templates, ha, hb] using identityTemplate_wellFormed (b:=1) arity ⟨i, h⟩

theorem sourceArity_eq : sourceArity (templates G u v U V) =
    Tables.adjoinedArity s arity U.exponent V.exponent := by
  funext i
  by_cases ha : i = s <;> by_cases hb : i = s+1 <;>
    simp [sourceArity, templates, Tables.adjoinedArity, ha, hb, identityTemplate]

def source : (i : Fin (s+2)) → Signature K (sourceArity (templates G u v U V) i.val) :=
  Tables.typed (Tables.familyTable G u v) (s+2) (sourceArity (templates G u v U V))

def scales (i : Fin (s+2)) : K :=
  (if i.val = s then U.scale else 1) * (if i.val = s+1 then V.scale else 1)

theorem network_value_of_eq (g h : Template)
    (hg : g.WellFormed s 1 arity) (hh : h.WellFormed s 1 arity)
    (he : g = h) (F : List Bool → K)
    (hv : (h.network hh G (fun _ => Signature.disequality)).denote =
      fun x => F (List.ofFn x)) :
    (g.network hg G (fun _ => Signature.disequality)).denote =
      fun x => F (List.ofFn x) := by
  cases he
  exact hv

/-- Local table equations are derived from the constructed macros and the
old identity templates; they are not an external correctness premise. -/
theorem local_value (i : Fin (s+2)) :
    ((templates G u v U V i.val).network (templates_valid G u v U V i.val i.isLt)
      G (fun _ => Signature.disequality)).denote =
        scales G u v U V i • source G u v U V i := by
  change ((templates G u v U V i.val).network _ G (fun _ => Signature.disequality)).denote =
    fun x => scales G u v U V i * Tables.familyTable G u v i.val (List.ofFn x)
  rcases i with ⟨i, hi⟩
  by_cases ha : i = s
  · subst i
    refine network_value_of_eq G (templates G u v U V s) U.labels.template _ U.labels.wellFormed
      (by simp [templates]) (fun bits => scales G u v U V ⟨s, hi⟩ *
        Tables.familyTable G u v s bits) ?_
    simpa [scales, Tables.familyTable, RawGrouping.withPower,
      Signature.unaryPower, List.map_ofFn, List.prod_ofFn] using U.value
  by_cases hb : i = s+1
  · subst i
    refine network_value_of_eq G (templates G u v U V (s+1)) V.labels.template _ V.labels.wellFormed
      (by simp [templates]) (fun bits => scales G u v U V ⟨s+1, hi⟩ *
        Tables.familyTable G u v (s+1) bits) ?_
    simpa [scales, Tables.familyTable, RawGrouping.withPower,
      Signature.unaryPower, List.map_ofFn, List.prod_ofFn] using V.value
  have his : i < s := by omega
  refine network_value_of_eq G (templates G u v U V i) (identityTemplate arity i) _
    (identityTemplate_wellFormed arity ⟨i, his⟩) (by simp [templates, ha, hb])
    (fun bits => scales G u v U V ⟨i, hi⟩ * Tables.familyTable G u v i bits) ?_
  rw [identityTemplate_denote arity ⟨i, his⟩ G (fun _ => Signature.disequality)]
  funext x
  simp [scales, ha, hb, Tables.familyTable, RawGrouping.withPower,
    Choice.table, his, List.getD_eq_getElem, identityTemplate]

/-- Existing raw replacement is applied literally, with no graph supplied
as a correctness hypothesis. -/
theorem physical_value (r : RawClosedNetwork)
    (hr : r.WellFormed (s+2) 1 (sourceArity (templates G u v U V))) :
    ((replace (templates G u v U V) r).realize
      (FixedGadgetSubstitution.query_wellFormed (templates G u v U V) r hr
        (templates_valid G u v U V)) G (fun _ => Signature.disequality)).denote Fin.elim0 =
      (U.scale ^ occurrences s r * V.scale ^ occurrences (s+1) r) *
        Choice.evaluate (Tables.familyTable G u v) r.edges.length r.vertices := by
  rw [replacement_partition (templates G u v U V) r hr (templates_valid G u v U V)
    (source G u v U V) G (fun _ => Signature.disequality) (scales G u v U V)
    (local_value G u v U V)]
  have hs : (∏ j, scales G u v U V (r.signatureLabel hr j)) =
      U.scale ^ occurrences s r * V.scale ^ occurrences (s+1) r := by
    unfold scales
    simp only [RawClosedNetwork.signatureLabel]
    rw [Finset.prod_mul_distrib, scale_product, scale_product]
  rw [hs]
  congr 1
  exact Tables.denote_eq_evaluate (Tables.familyTable G u v) r hr

abbrev UnaryInput := Input (s+2) 1 (Tables.adjoinedArity s arity 1 1)

def grouped (r : UnaryInput (s:=s) (arity:=arity)) : RawClosedNetwork :=
  GroupedQuery.query (Choice.table G) s (s+1) U.exponent V.exponent
    U.positive V.positive u v r

def IsLive (r : UnaryInput (s:=s) (arity:=arity)) : Prop :=
  Live (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1) (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive
    (residue s (s+1) U.exponent V.exponent U.positive V.positive r)

theorem grouped_valid (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    (grouped G u v U V r).WellFormed (s+2) 1 (sourceArity (templates G u v U V)) := by
  rw [sourceArity_eq, ← Tables.changed_adjoined]
  exact GroupedQuery.query_wellFormed (Choice.table G) s (s+1) U.exponent V.exponent
    U.positive V.positive (by omega) (by omega) (by omega)
    (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]) u v r h

/-- The emitted graph contains only the original Γ labels. -/
def emitted (r : UnaryInput (s:=s) (arity:=arity)) : RawClosedNetwork :=
  replace (templates G u v U V) (grouped G u v U V r)

theorem emitted_valid (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    (emitted G u v U V r).WellFormed s 1 arity :=
  FixedGadgetSubstitution.query_wellFormed (templates G u v U V) _
    (grouped_valid G u v U V r h) (templates_valid G u v U V)

def anchorScalar (r : UnaryInput (s:=s) (arity:=arity)) : K :=
  value (Tables.familyTable G u v)
    (anchor (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive
      (residue s (s+1) U.exponent V.exponent U.positive V.positive r) : UnaryInput (s:=s) (arity:=arity))

def normalization (r : UnaryInput (s:=s) (arity:=arity)) : K :=
  U.scale ^ occurrences s (grouped G u v U V r) *
    V.scale ^ occurrences (s+1) (grouped G u v U V r) * anchorScalar G u v U V r

theorem normalization_nonzero (r : UnaryInput (s:=s) (arity:=arity))
    (h : IsLive G u v U V r) : normalization G u v U V r ≠ 0 :=
  mul_ne_zero (mul_ne_zero (pow_ne_zero _ U.scale_ne_zero) (pow_ne_zero _ V.scale_ne_zero))
    (anchor_nonzero (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
      U.positive V.positive _ h)

theorem emitted_value (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    ((emitted G u v U V r).realize (emitted_valid G u v U V r h)
      G (fun _ => Signature.disequality)).denote Fin.elim0 =
      normalization G u v U V r * value (Tables.familyTable G u v) r := by
  rw [physical_value G u v U V _ (grouped_valid G u v U V r h)]
  rw [show Choice.evaluate (Tables.familyTable G u v) (grouped G u v U V r).edges.length
      (grouped G u v U V r).vertices = value (Tables.familyTable G u v) r * anchorScalar G u v U V r from
    GroupedQuery.query_value (Choice.table G) s (s+1) U.exponent V.exponent U.positive V.positive
      (by omega) (by simp [Tables.adjoinedArity]) (by simp [Tables.adjoinedArity]) u v r h]
  unfold normalization
  ring

/-- Exact original-Γ oracle recovery on live classes. Zero answers remain
valid: the denominator contains only fixed anchor values and macro scales. -/
theorem recover (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    ((emitted G u v U V r).realize (emitted_valid G u v U V r h)
      G (fun _ => Signature.disequality)).denote Fin.elim0 / normalization G u v U V r =
      value (Tables.familyTable G u v) r := by
  rw [emitted_value G u v U V r h]
  exact mul_div_cancel_left₀ _ (normalization_nonzero G u v U V r h)

theorem dead (r : UnaryInput (s:=s) (arity:=arity)) (h : ¬ IsLive G u v U V r) :
    value (Tables.familyTable G u v) r = 0 :=
  dead_value (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive r h

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.OriginalQuery
