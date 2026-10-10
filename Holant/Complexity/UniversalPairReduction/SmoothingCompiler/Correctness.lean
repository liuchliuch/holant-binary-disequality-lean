import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Compile
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.SearchFacts
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.EdgeFacts

/-! The executable pipeline computes the exact raw first-hit smoothing spec on
its original faithful at-most-one input. No transformed input promise is used. -/
namespace Holant.Complexity.UniversalPairReduction.SmoothingCompiler
open Turing Computability BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution RawClosedNetwork
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option synthInstance.maxSize 4096
set_option Elab.async false
variable (s : ℕ) (arity : ℕ → ℕ)

private theorem raw_ext {a b : RawClosedNetwork} (hv : a.vertices=b.vertices)
    (he : a.edges=b.edges) : a=b := by
  cases a; cases b; cases hv; cases he; rfl

theorem value_eq_compile (r : Input s arity) :
    value s r.val = ((Smoothing.compile s r.val).query,(Smoothing.compile s r.val).circle) := by
  have hf := filter_eq_search (fun row : RawVertex => row.1 == s) r.val.vertices r.property.2
  have hd := complement_filter_eq_erase (fun row : RawVertex => row.1 == s) r.val.vertices r.property.2
  cases hget : r.val.vertices[r.val.vertices.findIdx (fun row => row.1 == s)]? with
  | none =>
    have hz : r.val.vertices.filter (fun row => row.1 == s) = [] := by simpa [hget] using hf
    simp [value,present,FixedGadgetSubstitution.occurrences,hz,Smoothing.compile,hget]
  | some row =>
    have hsingle : r.val.vertices.filter (fun row => row.1 == s) = [row] := by simpa [hget] using hf
    have hlen := found_binary s arity r row hget
    rcases List.length_eq_two.mp hlen with ⟨first,second,hends⟩
    have hc : context s r.val = (first,second) := by
      simp [context,markedEnds,hsingle,hends]
    have hp : present s r.val = true := by simp [present,FixedGadgetSubstitution.occurrences,hsingle]
    have hrows : r.val.vertices.filter (fun row => row.1 != s) =
        r.val.vertices.eraseIdx (r.val.vertices.findIdx (fun row => row.1 == s)) := hd
    have hb := found_endpoints_bound s arity r row hget first second hends
    have heFirst := input_edges_eraseIdx_eq_replicate s arity r hb.1
    have heSecond := input_edges_eraseIdx_eq_replicate s arity r hb.2
    simp only [value,hp,reduceIte,Smoothing.compile,hget,Option.map_some,hends]
    unfold Smoothing.smoothAt
    by_cases he : first.1=second.1
    · simp only [if_pos he]
      apply Prod.ext
      · apply raw_ext
        · simp [residual,remainingRows,hc,hrows,remapRow,remap,he,Smoothing.emit]
        · simpa [residual,Smoothing.emit] using heFirst.symm
      · simp [circle,hc,he]
    · simp only [if_neg he]
      apply Prod.ext
      · apply raw_ext
        · simp [residual,remainingRows,hc,hrows,remapRow,remap,he,Smoothing.emit]
        · simpa [residual,Smoothing.emit] using heSecond.symm
      · simp [circle,hc,he]

/-- The final ordinary framed-pair witness uses exactly the source Input bytes. -/
noncomputable def computes : Computes (inputEncoding s arity) resultEncoding
    (fun r => ((Smoothing.compile s r.val).query,(Smoothing.compile s r.val).circle)) :=
  congrComputes (valueComputes s arity) (value_eq_compile s arity)

theorem inFP : InFP (inputEncoding s arity) resultEncoding
    (fun r => ((Smoothing.compile s r.val).query,(Smoothing.compile s r.val).circle)) :=
  (computes s arity).inFP

/-- Actual elementary Boolean instruction cost for the same compiler run. -/
theorem primitive_bound (r : Input s arity) :
    primitiveCost (computes s arity).machine ((computes s arity).outputs r).steps
      (some (initList (computes s arity).machine.computer ((inputEncoding s arity).encode r))) ≤
      (primitivePolynomial (computes s arity)).eval ((inputEncoding s arity).encode r).length :=
  computes_primitive_cost (computes s arity) r

end Holant.Complexity.UniversalPairReduction.SmoothingCompiler
