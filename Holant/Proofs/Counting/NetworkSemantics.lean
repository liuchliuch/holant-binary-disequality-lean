import Holant.Proofs.Counting.CircuitSemantics
import Holant.Complexity.ClosedNetworkCompleteness
import Mathlib.Tactic.IntervalCases
import Mathlib.Data.Complex.Basic


namespace Holant.LocalDrafts.CountingHardness.NetworkSemantics

open Holant Holant.Complexity RawCompiler CircuitSemantics
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
local instance : Fintype Bool := Bool.fintype

def extend {n : ℕ} (z : Fin n → Bool) (i : ℕ) : Bool :=
  if h : i < n then z ⟨i, h⟩ else false

@[simp] theorem extend_at {n : ℕ} (z : Fin n → Bool) (i : Fin n) : extend z i.val = z i := by
  simp [extend, i.isLt]

variable {K : Type*} [CommSemiring K]

theorem rowWeight_valid (r : RawVertex) (hi : r.1 < 5)
    (hlen : r.2.length = GateAlphabet.arity r.1) (ρ : ℕ → Bool) :
    rowWeight r ρ = GateAlphabet.signatures (K := K) ⟨r.1, hi⟩
      (fun j => ρ (r.2.get (Fin.cast hlen.symm j)).1) := by
  have hp (j : Fin (GateAlphabet.arity r.1)) :
      r.2.get (Fin.cast hlen.symm j) = r.2.getD j.val (0, false) := by
    exact (List.getD_eq_getElem r.2 (0, false) (by simpa [hlen] using j.isLt)).symm
  simp_rw [hp]
  rcases r with ⟨tag, ports⟩
  interval_cases tag <;>
    simp [rowWeight, GateAlphabet.arity, GateAlphabet.signatures, GateAlphabet.free, GateAlphabet.pin,
      GateAlphabet.copy, GateAlphabet.nand]

/-- Connect the executable raw row evaluator to the existing `Network.denote`. -/
theorem denote_eq_rows (r : RawClosedNetwork) (h : r.WellFormed 5 1 GateAlphabet.arity) :
    (r.realize h (GateAlphabet.signatures (K := K))
      (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 =
      ∑ z : Fin r.edges.length → Bool, rowsWeight r.vertices (extend z) := by
  change (Network.mk (r.shape h)
    (fun v x => GateAlphabet.signatures (r.signatureLabel h v) x)
    (fun _ => Signature.equality)).denote Fin.elim0 = _
  rw [Network.denote_equality]
  unfold Network.ordinaryDenote
  apply Finset.sum_congr rfl
  intro z _
  have hlist := List.ofFn_getElem_eq_map r.vertices
    (fun row => (rowWeight row (extend z) : K))
  change _ = (r.vertices.map (fun row => (rowWeight row (extend z) : K))).prod
  rw [← hlist, List.prod_ofFn]
  apply Finset.prod_congr rfl
  intro v _
  change GateAlphabet.signatures (r.signatureLabel h v) (fun j => z (r.route h ⟨v,j⟩).1) = rowWeight (r.vertices.get v) (extend z)
  rw [rowWeight_valid _ (h.1 v).1 (h.1 v).2]
  apply congrArg (GateAlphabet.signatures (r.signatureLabel h v))
  funext j
  change z (r.route h ⟨v, j⟩).1 =
    extend z ((r.vertices.get v).2.get (Fin.cast (h.1 v).2.symm j)).1
  exact (extend_at z (r.route h ⟨v, j⟩).1).symm

theorem compiled_rowsWeight (c : CircuitInstance)
    (z : Fin (c.inputs + freshEdges c.circuit) → Bool) :
    rowsWeight (K := K) (compile c).vertices (extend z) =
      weight c.circuit (fun i => z (Fin.castAdd _ i)) (fun i => z (Fin.natAdd c.inputs i)) := by
  have hs : rowsWeight (List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)])) (extend z) =
      (1 : K) := by simp [rowsWeight, List.map_ofFn, List.prod_ofFn, rowWeight]
  change rowsWeight ((List.ofFn fun i : Fin c.inputs => (0, [(i.val, false)])) ++
    rows c.circuit (fun i => (i.val, true)) c.inputs) (extend z) = _
  simp only [rowsWeight, List.map_append, List.prod_append] at hs ⊢
  rw [hs, one_mul]
  change rowsWeight (rows c.circuit (fun i => (i.val, true)) c.inputs) (extend z) = _
  rw [rowsWeight_eq]
  have hi : (fun i : Fin c.inputs => extend z i.val) = fun i => z (Fin.castAdd _ i) := by
    funext i
    exact extend_at z (Fin.castAdd _ i)
  have ht : (fun i : Fin (freshEdges c.circuit) => extend z (c.inputs + i.val)) =
      fun i => z (Fin.natAdd c.inputs i) := by
    funext i
    exact extend_at z (Fin.natAdd c.inputs i)
  rw [hi, ht]

/-- All allocated copy-wire choices are summed once; ignored original inputs
remain independently counted. The normalization factor is exactly one. -/
theorem compile_denote (c : CircuitInstance) :
    ((compile c).realize (compile_wellFormed c) (GateAlphabet.signatures (K := K))
      (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 =
      ∑ x : Fin c.inputs → Bool, if c.circuit.eval x then 1 else (0 : K) := by
  rw [denote_eq_rows]
  have he : (compile c).edges.length = c.inputs + freshEdges c.circuit := by simp [compile]
  let e : (Fin (compile c).edges.length → Bool) ≃
      (Fin (c.inputs + freshEdges c.circuit) → Bool) :=
    Equiv.arrowCongr (finCongr he) (Equiv.refl Bool)
  have hext (z : Fin (compile c).edges.length → Bool) : extend z = extend (e z) := by
    funext i
    unfold extend
    split_ifs with hi hj
    · rfl
    · omega
    · omega
    · rfl
  calc
    (∑ z : Fin (compile c).edges.length → Bool, rowsWeight (compile c).vertices (extend z)) =
        ∑ z : Fin (c.inputs + freshEdges c.circuit) → Bool,
          rowsWeight (compile c).vertices (extend z) := by
      apply Fintype.sum_equiv e
      intro z
      rw [hext]
    _ = ∑ z : Fin (c.inputs + freshEdges c.circuit) → Bool,
        weight c.circuit (fun i => z (Fin.castAdd _ i)) (fun i => z (Fin.natAdd c.inputs i)) := by
      apply Finset.sum_congr rfl
      intro z _
      exact compiled_rowsWeight c z
    _ = ∑ x : Fin c.inputs → Bool, if c.circuit.eval x then 1 else (0 : K) := by
      rw [sum_block]
      simp only [Fin.addCases_left, Fin.addCases_right]
      apply Finset.sum_congr rfl
      intro x _
      exact sum_weight c.circuit x

theorem compile_denote_nat (c : CircuitInstance) :
    ((compile c).realize (compile_wellFormed c) (GateAlphabet.signatures (K := ℕ))
      (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 = c.value :=
  compile_denote c

theorem compile_denote_complex (c : CircuitInstance) :
    ((compile c).realize (compile_wellFormed c) (GateAlphabet.signatures (K := ℂ))
      (fun _ : Fin 1 => Signature.equality)).denote Fin.elim0 = (c.value : ℂ) := by
  rw [compile_denote]
  simp [CircuitInstance.value, countAccepted]

end Holant.LocalDrafts.CountingHardness.NetworkSemantics
