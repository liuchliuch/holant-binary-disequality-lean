import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryEquality
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Complexity.BinaryInterpolation.SpectralForms

/-! Exact positive paired-series graphs implement matrix powers on four
physical boundary ports. All internal edges remain ordinary equality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCore
open Holant Holant.Complexity FixedGadgetSubstitution
open scoped BigOperators
namespace S
export GlobalCloseCompletionUnaryOrdinaryEquality (series series_value seriesLabels series_exact series_ordinary)
end S
namespace M
export OrdinaryNegativeCubicGadgets (Macro)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

def row (B : Matrix Bool Bool K) : Signature K 4 := fun x=>
  if x 0=x 2 ∧ x 1=x 3 then B (x 0) (x 1) else 0

theorem identity : row (1 : Matrix Bool Bool K)=Holant.EightVertex.ProductAnchor.equalityFour := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [row,Holant.EightVertex.ProductAnchor.equalityFour,Matrix.one_apply,funext_iff,Fin.forall_fin_succ,Fin.exists_fin_succ,h0,h1,h2,h3]

theorem smul (c : K) (B : Matrix Bool Bool K) : row (c • B)=c • row B := by
  funext x
  simp only [row,Matrix.smul_apply,Pi.smul_apply,smul_eq_mul]
  split_ifs <;> simp

theorem add (B C : Matrix Bool Bool K) : row (B+C)=row B+row C := by
  funext x
  simp only [row,Matrix.add_apply,Pi.add_apply]
  split_ifs <;> simp

theorem series_value (B C : Matrix Bool Bool K) (x : Fin 4→Bool) :
    (∑u : Bool,∑v : Bool,row B ![x 0,u,x 2,v]*row C ![u,x 1,v,x 3])=row (B*C) x := by
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [row,Matrix.mul_apply,Fintype.sum_bool,h0,h1,h2,h3]

variable {s : ℕ} {a : ℕ→ℕ} {H : (i : Fin s)→Signature K (a i.val)}

def series (N Q : M.Macro H 4) : M.Macro H 4 where
  network:=S.series N.network Q.network
  labels:=S.seriesLabels N.network Q.network N.labels Q.labels
  exact:=S.series_exact H N.network Q.network N.labels Q.labels N.exact Q.exact
  edges:=S.series_ordinary N.network Q.network N.edges Q.edges

theorem series_denote (N Q : M.Macro H 4) (B C : Matrix Bool Bool K)
    (hN : N.network.denote=row B) (hQ : Q.network.denote=row C) :
    (series N Q).network.denote=row (B*C) := by
  funext x
  rw [series,S.series_value,hN,hQ,series_value]

def power (N : M.Macro H 4) : ℕ→M.Macro H 4
  | 0=>N
  | k+1=>series N (power N k)

theorem power_denote (N : M.Macro H 4) (B : Matrix Bool Bool K)
    (hN : N.network.denote=row B) (k : ℕ) :
    (power N k).network.denote=row (B^(k+1)) := by
  induction k with
  | zero=>simpa only [power,Nat.zero_add,pow_one] using hN
  | succ k ih=>rw [power,series_denote N (power N k) B (B^(k+1)) hN ih,←pow_succ']

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCore
end
