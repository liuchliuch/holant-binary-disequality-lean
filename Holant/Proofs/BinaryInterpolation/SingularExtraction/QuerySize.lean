import Holant.Proofs.BinaryInterpolation.SingularExtraction.OriginalQuery
import Holant.Complexity.FixedGadgetSubstitution.Size


noncomputable section
namespace Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.OriginalQuery
open Holant Holant.Complexity Holant.Complexity.FixedGadgetSubstitution
open Holant.Complexity.UniversalPairReduction.Surgery
open RawClosedNetwork ResidueAnchors RawGrouping
variable {K : Type} [Field K] {s : ℕ} {arity : ℕ → ℕ}
variable (G : (i : Fin s) → Signature K (arity i.val)) (u v : Bool → K)
variable (U : PowerMacro G u) (V : PowerMacro G v)

def macroSize : ℕ := 1 + U.labels.template.vertices.length + U.labels.template.edges.length +
  V.labels.template.vertices.length + V.labels.template.edges.length

theorem template_size (i : ℕ) :
    (templates G u v U V i).vertices.length + (templates G u v U V i).edges.length ≤
      macroSize G u v U V := by
  by_cases ha : i = s <;> by_cases hb : i = s+1 <;>
    simp [templates, ha, hb, identityTemplate, macroSize] <;> omega

theorem replacement_size (r : RawClosedNetwork) :
    (replace (templates G u v U V) r).vertices.length +
        (replace (templates G u v U V) r).edges.length ≤
      macroSize G u v U V * (r.vertices.length + r.edges.length) := by
  have hs : ∀ rows : List RawVertex,
      (rows.map (fun row => (templates G u v U V row.1).vertices.length)).sum +
        (rows.map (fun row => (templates G u v U V row.1).edges.length)).sum ≤
          macroSize G u v U V * rows.length := by
    intro rows
    induction rows with
    | nil => simp
    | cons row rows ih =>
      have ht := template_size G u v U V row.1
      simp only [List.map_cons, List.sum_cons, List.length_cons, Nat.mul_succ]
      omega
  have ht := hs r.vertices
  have hc : 1 ≤ macroSize G u v U V := by simp [macroSize]; omega
  have he := Nat.mul_le_mul_right r.edges.length hc
  rw [replace_vertex_count, replace_edge_count]
  nlinarith

theorem grouped_size (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    (grouped G u v U V r).vertices.length + (grouped G u v U V r).edges.length ≤
      (augmented (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
        U.positive V.positive r).val.vertices.length +
      (augmented (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
        U.positive V.positive r).val.edges.length := by
  let t := augmented (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive r
  have hd := augmented_counts (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
    U.positive V.positive r h
  have hda := GroupedQuery.selected_dvd_of_occurrences s U.exponent t
    (by simp [Tables.adjoinedArity]) hd.1
  have hw := groupOne_wellFormed s U.exponent (by omega : s < s+2) t.val t.property hda
  have h₁ := groupOne_vertex_bound_valid s U.exponent U.positive t.val t.property
    (by simp [Tables.adjoinedArity])
  have h₂ := groupOne_vertex_bound_valid (s+1) V.exponent V.positive
    (groupOne s U.exponent t.val) hw (by simp [changedArity, Tables.adjoinedArity])
  change (groupOne (s+1) V.exponent (groupOne s U.exponent t.val)).vertices.length +
    t.val.edges.length ≤ t.val.vertices.length + t.val.edges.length
  omega

/-- A single bound on actual query vertices plus edges in terms of original
serialized input length, not the length of an already expanded query. -/
theorem emitted_size (r : UnaryInput (s:=s) (arity:=arity)) (h : IsLive G u v U V r) :
    (emitted G u v U V r).vertices.length + (emitted G u v U V r).edges.length ≤
      macroSize G u v U V *
        ((RawClosedNetwork.encoding.encode r.val).length +
          anchorSize (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1)
            (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive) := by
  exact (replacement_size G u v U V _).trans
    (Nat.mul_le_mul_left _ ((grouped_size G u v U V r h).trans
      (augmented_size (Tables.familyTable G u v) s (s+1) U.exponent V.exponent
        U.positive V.positive r)))

def arityBound : ℕ := (Finset.range s).sup arity

theorem arity_le_bound (i : ℕ) (hi : i < s) : arity i ≤ arityBound (s:=s) (arity:=arity) :=
  Finset.le_sup (f:=arity) (Finset.mem_range.mpr hi)

/-- The actual complete raw query has quadratic encoded size in original
input bytes. Constants include the anchor table and all original arities. -/
def encodingPolynomial : Polynomial ℕ :=
  let C := macroSize G u v U V
  let D := anchorSize (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1)
    (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive
  let A := arityBound (s:=s) (arity:=arity)
  let z := Polynomial.C C * (Polynomial.X + Polynomial.C D)
  2 * ((2 * (2 * Polynomial.C s + 2 + (4*z+6) * Polynomial.C A) + 2)*z+1)+1+(4*z+1)

theorem emitted_encoding_length (r : UnaryInput (s:=s) (arity:=arity))
    (h : IsLive G u v U V r) :
    (RawClosedNetwork.encoding.encode (emitted G u v U V r)).length ≤
      (encodingPolynomial G u v U V).eval (RawClosedNetwork.encoding.encode r.val).length := by
  have hr := raw_length_le (emitted G u v U V r) (emitted_valid G u v U V r h)
    (arityBound (s:=s) (arity:=arity)) (arity_le_bound (s:=s) (arity:=arity))
  have hc := emitted_size G u v U V r h
  let z := macroSize G u v U V * ((RawClosedNetwork.encoding.encode r.val).length +
    anchorSize (s:=s+2) (b:=1) (arity:=Tables.adjoinedArity s arity 1 1)
      (Tables.familyTable G u v) s (s+1) U.exponent V.exponent U.positive V.positive)
  have hv : (emitted G u v U V r).vertices.length ≤ z := by dsimp [z]; omega
  have he : (emitted G u v U V r).edges.length ≤ z := by dsimp [z]; omega
  apply hr.trans
  have hm := Nat.mul_le_mul_right (arityBound (s:=s) (arity:=arity))
    (Nat.add_le_add_right (Nat.mul_le_mul_left 4 he) 6)
  have ht := Nat.mul_le_mul
    (Nat.add_le_add_right (Nat.mul_le_mul_left 2 (Nat.add_le_add_left hm (2*s+2))) 2) hv
  have hE := Nat.mul_le_mul_left 4 he
  simp only [encodingPolynomial, Polynomial.eval_add, Polynomial.eval_mul,
    Polynomial.eval_C, Polynomial.eval_X, Polynomial.eval_ofNat, Polynomial.eval_one]
  change _ ≤ 2 * ((2 * (2*s+2+(4*z+6)*arityBound (s:=s) (arity:=arity))+2)*z+1)+1+(4*z+1)
  norm_num at hr ⊢
  omega

end Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.OriginalQuery
