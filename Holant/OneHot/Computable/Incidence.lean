import Holant.Complexity.ClosedNetworkSemantics
import Holant.OneHot.Decomposition.Rooted

/-!
# Executable recovery of original ordered port occurrences

The input is the project's actual framed `RawClosedNetwork`, not a black-box
endpoint oracle. Searching its explicit port list computes the inverse incidence
permutation. The proofs below identify that inverse with the existing semantics.
No complexity claim is made for the semantic `shape` implementation itself.
-/

namespace Holant.OneHot.Computable

open Holant.Complexity Holant.Complexity.RawClosedNetwork

/-- Linear search with an actual counter: one predicate evaluation per examined
list entry. The predicate's implementation cost is deliberately not hidden in a
machine-time claim. -/
def search {α : Type} (p : α → Bool) : List α → Option α × ℕ
  | [] => (none, 0)
  | a :: as => if p a then (some a, 1)
    else let tail := search p as; (tail.1, tail.2 + 1)

@[simp] theorem search_value {α : Type} (p : α → Bool) (as : List α) :
    (search p as).1 = as.find? p := by
  induction as with
  | nil => rfl
  | cons a as ih => cases hp : p a <;> simp [search, List.find?, ih, hp]

theorem search_work_le {α : Type} (p : α → Bool) (as : List α) :
    (search p as).2 ≤ as.length := by
  induction as with
  | nil => simp [search]
  | cons a as ih => simp only [search]; split <;> simp_all

end Holant.OneHot.Computable

namespace Holant.Complexity.RawClosedNetwork

open Holant.OneHot.Computable

variable {s b : ℕ} {arity : ℕ → ℕ} (r : Holant.Complexity.RawClosedNetwork)

/-- Enumerate positions of the stored port lists, preserving vertex and port
order. The loop bounds are stored list lengths, never endpoint identifier values. -/
def occurrences (h : r.WellFormed s b arity) : List (r.Ports arity) :=
  (List.finRange r.vertices.length).flatMap fun v =>
    (List.finRange (r.vertices.get v).2.length).map fun i =>
      ⟨v, Fin.cast (h.1 v).2 i⟩

@[simp] theorem mem_occurrences (h : r.WellFormed s b arity) (p : r.Ports arity) :
    p ∈ r.occurrences h := by
  rcases p with ⟨v, i⟩
  apply List.mem_flatMap.mpr
  refine ⟨v, List.mem_finRange _, ?_⟩
  apply List.mem_map.mpr
  exact ⟨Fin.cast (h.1 v).2.symm i, List.mem_finRange _, by simp⟩

@[simp] theorem occurrences_length (h : r.WellFormed s b arity) :
    (r.occurrences h).length = 2 * r.edges.length := by
  have he : r.endpoints.length = 2 * r.edges.length := by
    rw [h.2.2.length_eq, expectedEndpoints_length, Nat.mul_comm]
  rw [occurrences, List.length_flatMap]
  simp only [List.length_map, List.length_finRange]
  rw [← List.ofFn_eq_map]
  have hv := List.ofFn_getElem_eq_map r.vertices (fun v : RawVertex => v.2.length)
  simp only [List.get_eq_getElem]
  rw [hv]
  simpa [endpoints, List.length_flatten, List.map_map, Function.comp_def] using he

/-- Search one original edge end in the explicit ordered occurrence table. -/
def lookupRun (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    Option (r.Ports arity) × ℕ :=
  search (fun p => decide (r.route h p = q)) (r.occurrences h)

theorem lookupRun_isSome (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    (r.lookupRun h q).1.isSome := by
  rw [lookupRun, search_value, List.find?_isSome]
  obtain ⟨p, hp⟩ := r.route_surjective h q
  exact ⟨p, r.mem_occurrences h p, by simp [hp]⟩

/-- This inverse is executable: no `Classical.choose`, quotient enumeration, or
function inverse is used to compute it. -/
def lookup (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) : r.Ports arity :=
  (r.lookupRun h q).1.get (r.lookupRun_isSome h q)

@[simp] theorem route_lookup (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    r.route h (r.lookup h q) = q := by
  have hh : (r.lookupRun h q).1 = some (r.lookup h q) :=
    (Option.some_get (r.lookupRun_isSome h q)).symm
  rw [lookupRun, search_value] at hh
  have hp := List.find?_some (p := fun p => decide (r.route h p = q)) hh
  exact of_decide_eq_true hp

@[simp] theorem lookup_route (h : r.WellFormed s b arity) (p : r.Ports arity) :
    r.lookup h (r.route h p) = p :=
  (r.route_bijective h).1 (r.route_lookup h _)

/-- Effective port permutation, retaining both the local port number and edge
orientation. It has the same forward map as the decoded semantic permutation. -/
def incidenceEquiv (h : r.WellFormed s b arity) :
    r.Ports arity ≃ (Fin r.edges.length × Bool) where
  toFun := r.route h
  invFun := r.lookup h
  left_inv := r.lookup_route h
  right_inv := r.route_lookup h

@[simp] theorem incidenceEquiv_eq (h : r.WellFormed s b arity) :
    r.incidenceEquiv h = r.portEquiv h := by
  apply Equiv.ext
  intro p
  rfl

/-- One lookup inspects at most the explicitly stored `2E` endpoint occurrences. -/
theorem lookupRun_work_le (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    (r.lookupRun h q).2 ≤ 2 * r.edges.length := by
  simpa [lookupRun] using search_work_le (fun p => decide (r.route h p = q)) (r.occurrences h)

/-- Every original edge is retained in input order, including loops and repeated
pairs. Both endpoint records retain their original local port positions. -/
def edgePorts (h : r.WellFormed s b arity) : List (r.Ports arity × r.Ports arity) :=
  List.ofFn fun e : Fin r.edges.length => (r.lookup h (e, false), r.lookup h (e, true))

@[simp] theorem edgePorts_length (h : r.WellFormed s b arity) :
    (r.edgePorts h).length = r.edges.length := by simp [edgePorts]

/-- Agreement with the old semantic inverse, on each individual edge end. -/
theorem lookup_eq_semantic (h : r.WellFormed s b arity) (q : Fin r.edges.length × Bool) :
    r.lookup h q = (r.shape h).closedPorts.symm q := by
  apply (r.route_bijective h).1
  rw [r.route_lookup h]
  have hx := (r.shape h).closedPorts.apply_symm_apply q
  exact hx.symm

/-- The recovered endpoint is the original semantic vertex, not a renumbered or
simple-graph surrogate. -/
theorem lookup_vertex (h : r.WellFormed s b arity) (e : Fin r.edges.length) (z : Bool) :
    (r.lookup h (e, z)).1 = (r.shape h).endpoint e z := by
  rw [r.lookup_eq_semantic h]
  rfl

end Holant.Complexity.RawClosedNetwork
