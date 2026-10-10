import Holant.Certificates.TetrahedralPreservers.FullRankRaw

/-! Integer identities witnessing that every signed identity stabilizer is
a quaternion conjugation or a quaternion conjugation after transpose. -/
namespace Holant.Certificates.TetrahedralPreservers
open scoped Matrix
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def zOcta : Fin 24 → ZV :=
  ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1],
    ![1,1,1,1],![1,1,1,-1],![1,1,-1,1],![1,1,-1,-1],
    ![1,-1,1,1],![1,-1,1,-1],![1,-1,-1,1],![1,-1,-1,-1],
    ![1,1,0,0],![1,-1,0,0],![1,0,1,0],![1,0,-1,0],![1,0,0,1],![1,0,0,-1],
    ![0,1,1,0],![0,1,-1,0],![0,1,0,1],![0,1,0,-1],![0,0,1,1],![0,0,1,-1]]

def zLeft (p : ZV) : ZEnd :=
  ![![p 0,-p 1,-p 2,-p 3],![p 1,p 0,p 3,-p 2],
    ![p 2,-p 3,p 0,p 1],![p 3,p 2,-p 1,p 0]]
def zRight (p : ZV) : ZEnd :=
  ![![p 0,-p 1,-p 2,-p 3],![p 1,p 0,-p 3,p 2],
    ![p 2,p 3,p 0,-p 1],![p 3,-p 2,p 1,p 0]]
def zConj (p : ZV) : ZV := ![p 0,-p 1,-p 2,-p 3]
def zNorm (p : ZV) : ℤ := (p 0)^2+(p 1)^2+(p 2)^2+(p 3)^2
def zTranspose (b : Bool) : ZEnd := Matrix.diagonal ![1,1,if b then -1 else 1,1]

def permutationCode (σ : Equiv.Perm (Fin 3)) : Fin 6 :=
  if σ 0=0 then if σ 1=1 then 0 else 1
  else if σ 0=1 then if σ 1=0 then 2 else 3 else if σ 1=0 then 4 else 5
def signCode (ε : Fin 3 → Bool) : Fin 8 :=
  ⟨(if ε 0 then 4 else 0)+(if ε 1 then 2 else 0)+(if ε 2 then 1 else 0),by split_ifs <;> omega⟩
def normalCode (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : Fin 48 :=
  ⟨8*(permutationCode σ).val+(signCode ε).val,by omega⟩
def normalIndexTable : Fin 48 → Fin 24 :=
  ![0,1,0,1,3,2,3,2,12,13,12,13,22,23,22,23,17,18,17,18,16,19,16,19,
    11,5,11,5,6,8,6,8,4,9,4,9,7,10,7,10,20,14,20,14,15,21,15,21]
def normalTransposeTable : Fin 48 → Bool :=
  ![false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false,
    true,false,false,true,false,true,true,false,false,true,true,false,true,false,false,true,
    false,true,true,false,true,false,false,true,true,false,false,true,false,true,true,false]
def normalVector (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : ZV :=
  zOcta (normalIndexTable (normalCode σ ε))
def normalTranspose (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : Bool :=
  normalTransposeTable (normalCode σ ε)

theorem normal_identity : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    zLeft (normalVector σ ε) * zRight (zConj (normalVector σ ε)) *
      zTranspose (normalTranspose σ ε) = zNorm (normalVector σ ε) • signedRaw σ ε := by
  intro σ ε
  fin_cases σ <;> fin_cases ε <;> decide +kernel

theorem zOcta_norm_ne_zero : ∀ k : Fin 24, zNorm (zOcta k) ≠ 0 := by decide +kernel

theorem normal_norm_ne_zero (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) :
    zNorm (normalVector σ ε) ≠ 0 := zOcta_norm_ne_zero _

theorem zstandard_norm_ne_zero : ∀ k : Fin 12, zNorm (zstandard k) ≠ 0 := by decide +kernel

end Holant.Certificates.TetrahedralPreservers
