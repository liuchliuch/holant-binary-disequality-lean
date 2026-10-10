import Holant.Proofs.Hardness.EightVertexGaugeTwoRowNetwork
import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients

/-! Exact native-X series for complement-symmetric eight-vertex rows.
The four Bell coordinates multiply independently under the actual two-edge
connection. Binary-cap order does not constrain these quaternary coordinates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Series
open Holant
namespace E
export Holant.LocalDrafts.Hardness.EightVertexNonexception (table Entries)
end E
namespace G
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EightVertexGaugeTwoRowNetwork
  (connect connect_denote term)
end G
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

def row (a b c d : K) : Signature K 4:=E.table ⟨a,b,c,d,d,c,b,a⟩
def spectrum (a b c d : K) : Fin 4→K:=![a+b,b-a,c+d,d-c]
def ofSpectrum (v : Fin 4→K) : Signature K 4:=
  row ((v 0-v 1)/2) ((v 0+v 1)/2) ((v 2-v 3)/2) ((v 2+v 3)/2)

theorem reconstruct [CharZero K] (a b c d : K) : ofSpectrum (spectrum a b c d)=row a b c d := by
  change row ((a+b-(b-a))/2) ((a+b+(b-a))/2) ((c+d-(d-c))/2) ((c+d+(d-c))/2)=row a b c d
  congr 1 <;> ring

theorem connected (L R : Network K 4) (a b c d p q r s : K)
    (left : L.denote=row a b c d) (right : R.denote=row p q r s) :
    (G.connect L R false).denote=row (a*q+b*p) (a*p+b*q) (c*s+d*r) (c*r+d*s) := by
  funext x
  rw [G.connect_denote,left,right]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [G.term,row,E.table,h0,h1,h2,h3] <;> ring

theorem connected_spectrum [CharZero K] (L R : Network K 4) (u v : Fin 4→K)
    (left : L.denote=ofSpectrum u) (right : R.denote=ofSpectrum v) :
    (G.connect L R false).denote=ofSpectrum (fun i=>u i*v i) := by
  rw [ofSpectrum] at left right
  rw [connected L R _ _ _ _ _ _ _ _ left right]
  unfold ofSpectrum
  congr 1 <;> ring

def power (q : Signature K 4) : ℕ→Network K 4
  | 0=>Network.corolla q
  | n+1=>G.connect (power q n) (Network.corolla q) false

theorem power_value [CharZero K] (v : Fin 4→K) (n : ℕ) :
    (power (ofSpectrum v) n).denote=ofSpectrum (fun i=>v i^(n+1)) := by
  induction n with
  | zero=>simp [power]
  | succ n ih=>
    rw [power,connected_spectrum _ _ _ _ ih (Network.denote_corolla _)]
    congr 1
    funext i
    exact (pow_succ (v i) (n+1)).symm

theorem row_power [CharZero K] (a b c d : K) (n : ℕ) :
    (power (row a b c d) n).denote=ofSpectrum (fun i=>(spectrum a b c d i)^(n+1)) := by
  rw [←reconstruct a b c d]
  exact power_value (spectrum a b c d) n

def diagonal (sign : K) : Signature K 2:=fun x=>
  if x 0 then (if x 1 then sign else 0) else (if x 1 then 0 else 1)

theorem first_projector [CharZero K] :
    ofSpectrum (![1,0,0,0] : Fin 4→K)=fun x=>(2:K)⁻¹*Signature.tensor (diagonal 1) (diagonal 1) x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [ofSpectrum,row,E.table,Signature.tensor_apply,diagonal,h0,h1,h2,h3,div_eq_mul_inv]

theorem second_projector [CharZero K] :
    ofSpectrum (![0,1,0,0] : Fin 4→K)=fun x=>-(2:K)⁻¹*Signature.tensor (diagonal (-1)) (diagonal (-1)) x := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
    simp [ofSpectrum,row,E.table,Signature.tensor_apply,diagonal,h0,h1,h2,h3,div_eq_mul_inv]

theorem example_spectrum : spectrum (2:ℚ) 1 1 1=![3,-1,2,0] := by
  norm_num [spectrum]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4Series
end
