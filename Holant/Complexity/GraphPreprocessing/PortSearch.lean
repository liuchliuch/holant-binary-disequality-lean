import Holant.Complexity.GraphPreprocessing.FramedFind
import Holant.OneHot.Computable.Incidence
import Mathlib.Data.List.Nodup

/-! Operational inverse lookup within an original vertex's stored port list.
The uniqueness needed for the first-match theorem is derived from the validated
original incidence permutation, never supplied as a search certificate. -/
namespace Holant.Complexity.GraphPreprocessing.FramedFind
open Turing StackProtocol Computability

theorem find_get_exact {α : Type} (e : Encoding α Bool) (xs : List α) (i : Fin xs.length)
    (hnd : xs.Nodup) (suffix counter : List Bool) :
    RunsExactly machine.computer.step
      (config 0 true (framedListEncode e xs ++ suffix) (e.encode (xs.get i)) [] [] [] [] counter)
      (config 6 true (framedListEncode e (xs.drop (i.val + 1)) ++ suffix) (e.encode (xs.get i)) [] [] [] []
        (List.replicate i.val true ++ counter)) (ticks e (xs.get i) (xs.take i.val)) := by
  have hx : xs.take i.val ++ xs.get i :: xs.drop (i.val + 1) = xs := by
    rw [List.get_eq_getElem, List.getElem_cons_drop i.isLt, List.take_append_drop]
  have hn : (xs.take i.val).length = i.val := by simp
  have hpre : ∀ a ∈ xs.take i.val, a ≠ xs.get i := by
    intro a ha he
    obtain ⟨j, hj, hjv⟩ := List.mem_iff_getElem.mp ha
    have hj' : j < i.val := by simpa only [hn] using hj
    have hjl : j < xs.length := Nat.lt_trans hj' i.isLt
    have hv : xs[j] = xs[i.val] := by simpa [List.get_eq_getElem] using hjv.trans he
    have hi := hnd.eq_of_getElem_eq hjl i.isLt hv
    omega
  simpa only [hx, hn] using find_exact e (xs.get i) (xs.take i.val) (xs.drop (i.val + 1)) hpre suffix counter

end Holant.Complexity.GraphPreprocessing.FramedFind

namespace Holant.Complexity.GraphPreprocessing.PortSearch
open Turing StackProtocol Computability RawClosedNetwork

/-- Duplicate original endpoint records are ruled out by actual route injectivity. -/
theorem vertex_ports_nodup {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) (v : Fin r.vertices.length) : (r.vertices.get v).2.Nodup := by
  apply List.nodup_iff_injective_get.mpr
  intro i j hij
  let p : r.Ports arity := ⟨v, Fin.cast (h.1 v).2 i⟩
  let q : r.Ports arity := ⟨v, Fin.cast (h.1 v).2 j⟩
  have hp : r.portEndpoint h p = r.portEndpoint h q := by simpa [portEndpoint, p, q] using hij
  have hr : r.route h p = r.route h q := by
    apply Prod.ext
    · apply Fin.ext
      exact congrArg Prod.fst hp
    · change (r.portEndpoint h p).2 = (r.portEndpoint h q).2
      exact congrArg Prod.snd hp
  have he := (r.route_bijective h).1 hr
  exact Fin.ext (congrArg (fun p : r.Ports arity => p.2.val) he)

/-- A machine search for an original edge end returns its original local port
number. The search executes every preceding candidate's actual bit comparison. -/
theorem search_original_port {s b : ℕ} {arity : ℕ → ℕ} (r : RawClosedNetwork)
    (h : r.WellFormed s b arity) (p : r.Ports arity) (suffix counter : List Bool) :
    RunsExactly FramedFind.machine.computer.step
      (FramedFind.config 0 true (framedListEncode endpointEncoding (r.vertices.get p.1).2 ++ suffix)
        (endpointEncoding.encode ((r.route h p).1.val, (r.route h p).2)) [] [] [] [] counter)
      (FramedFind.config 6 true
        (framedListEncode endpointEncoding ((r.vertices.get p.1).2.drop (p.2.val + 1)) ++ suffix)
        (endpointEncoding.encode ((r.route h p).1.val, (r.route h p).2)) [] [] [] []
        (List.replicate p.2.val true ++ counter))
      (FramedFind.ticks endpointEncoding (r.portEndpoint h p) ((r.vertices.get p.1).2.take p.2.val)) :=
  FramedFind.find_get_exact endpointEncoding (r.vertices.get p.1).2 (Fin.cast (h.1 p.1).2.symm p.2)
    (vertex_ports_nodup r h p.1) suffix counter

end Holant.Complexity.GraphPreprocessing.PortSearch
