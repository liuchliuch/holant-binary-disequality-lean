import Holant.Proofs.Hardness.GeneralEOTensorPowerRemovalValue
import Holant.Proofs.Reductions.GeneralExtraction.Carrier

/-! The literal list tensor rows are the project's copy-major `blockPower`.
This bridge identifies the raw assignment sum with the ordinary original
validated network semantics; it does not introduce a substitute evaluator. -/
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalTables
open Holant Holant.Complexity GeneralEOTensorPowerRemovalRaw GeneralEOTensorPowerRemovalValue
open UniversalPairReduction.Surgery
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [CommSemiring K]

def listValue {n : ℕ} (f : Signature K n) (bits : List Bool) : K :=
  f (fun i=>bits.getD i.val false)

def signatures {s : ℕ} (a : ℕ→ℕ) (F : Choice.Table K) (i : Fin s) : Signature K (a i.val) :=
  fun x=>F i.val (List.ofFn x)

theorem ofFn_getD (bits : List Bool) (n : ℕ) (h : bits.length=n) :
    List.ofFn (fun i : Fin n=>bits.getD i.val false)=bits := by
  apply List.ext_getElem (by simp [h])
  intro i hi hj
  simp only [List.getElem_ofFn]
  exact List.getD_eq_getElem bits false hj

theorem table_signatures {s : ℕ} (a : ℕ→ℕ) (F : Choice.Table K)
    (i : ℕ) (hi : i<s) (bits : List Bool) (h : bits.length=a i) :
    Choice.table (signatures (s:=s) a F) i bits=F i bits := by
  simp only [Choice.table,dite_eq_left hi,signatures,ofFn_getD bits _ h]

theorem rowValue_table {s b : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed s b a) (F : Choice.Table K) (c : ℕ→Bool) (v : RawVertex)
    (hv : v∈r.vertices) :
    Choice.rowValue (Choice.table (signatures (s:=s) a F)) c v=Choice.rowValue F c v := by
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hv
  exact table_signatures a F _ (hr.1 i).1 _ (by simpa using (hr.1 i).2)

/-- Raw-table evaluation is proved equal to the unchanged native decoder. -/
theorem denote {s : ℕ} {a : ℕ→ℕ} (r : RawClosedNetwork) (hr : r.WellFormed s 1 a)
    (F : Choice.Table K) :
    (r.realize hr (signatures a F) (fun _=>Signature.disequality)).denote Fin.elim0=
      Choice.evaluate F r.edges.length r.vertices := by
  rw [Choice.denote_eq_evaluate]
  unfold Choice.evaluate
  apply Finset.sum_congr rfl
  intro c _
  unfold Choice.weight
  congr 1
  apply List.map_congr_left
  intro v hv
  exact rowValue_table hr F (Choice.extend c) v hv

theorem tensorList_prod (n k : ℕ) (f : List Bool→K) (bs : List Bool) :
    tensorList n f k bs=∏j : Fin k,f ((bs.drop (n*j.val)).take n) := by
  induction k generalizing bs with
  | zero => simp [tensorList]
  | succ k ih =>
    simp only [tensorList,Fin.prod_univ_succ,Fin.val_zero,Nat.mul_zero,List.drop_zero,
      Fin.val_succ,ih]
    congr 1
    apply Finset.prod_congr rfl
    intro j _
    simp [List.drop_drop,Nat.mul_add,Nat.add_comm]

/-- Literal copy-major product, including n=0 and k=0. -/
theorem tensorList_blockPower {n : ℕ} (f : Signature K n) (k : ℕ) (x : Fin (k*n)→Bool) :
    tensorList n (listValue f) k (List.ofFn x)=
      Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier.blockPower f k x := by
  rw [tensorList_prod]
  unfold Holant.LocalDrafts.Hardness.GeneralExtraction.Carrier.blockPower
  apply Finset.prod_congr rfl
  intro j _
  unfold listValue
  congr 1
  funext i
  have hj : n*j.val+n≤k*n := by
    have hh := Nat.mul_le_mul_right n (Nat.succ_le_of_lt j.isLt)
    simpa [Nat.add_mul,Nat.mul_add,Nat.mul_comm] using hh
  have hb : i.val<(((List.ofFn x).drop (n*j.val)).take n).length := by
    simp only [List.length_take,List.length_drop,List.length_ofFn]
    omega
  rw [List.getD_eq_getElem _ _ hb]
  simp only [List.getElem_take,List.getElem_drop,List.getElem_ofFn]
  congr 1
  apply Fin.ext
  simp [finProdFinEquiv,Nat.add_comm]

/-- Ordinary decoded target query has precisely the source value. -/
theorem grouping_denote {s n k : ℕ} {a : ℕ→ℕ} {r : RawClosedNetwork}
    (hr : r.WellFormed (s+1) 1 (sourceArity s n a)) (h : count s r%k=0)
    (F : Choice.Table K) (f : Signature K n) :
    ((raw s k r).realize (wellFormed hr h)
      (signatures (targetArity s n k a) (targetTable s n k F (listValue f)))
      (fun _=>Signature.disequality)).denote Fin.elim0=
    (r.realize hr (signatures (sourceArity s n a) (sourceTable s F (listValue f)))
      (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [denote,denote]
  exact evaluate_eq hr h F (listValue f)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOTensorPowerRemovalTables
