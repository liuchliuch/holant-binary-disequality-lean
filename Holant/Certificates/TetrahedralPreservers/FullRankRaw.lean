import Holant.Certificates.TetrahedralPreservers.StandardGeometry

/-! Small integer certificates for the 12 left translations and 48 signed
identity stabilizers. They certify candidates only; completeness is separate. -/
namespace Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix
set_option maxRecDepth 1000000
set_option maxHeartbeats 20000000

abbrev ZV := Fin 4 → ℤ
abbrev ZEnd := Matrix (Fin 4) (Fin 4) ℤ

def zstandard : Fin 12 → ZV :=
  ![![1,0,0,0],![0,1,0,0],![0,0,1,0],![0,0,0,1],
    ![1,1,1,1],![1,1,1,-1],![1,1,-1,1],![1,1,-1,-1],
    ![1,-1,1,1],![1,-1,1,-1],![1,-1,-1,1],![1,-1,-1,-1]]

def zsign (b : Bool) : ℤ := if b then -1 else 1
def zJ : ZEnd := Matrix.diagonal ![1,-1,1,-1]
def zsharp (A : ZEnd) : ZEnd := zJ*A.transpose*zJ

def signedRaw (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool) : ZEnd := fun i j =>
  Fin.cases ((Pi.single (0 : Fin 4) (1 : ℤ) : ZV) i)
    (fun k => zsign (ε k) * (Pi.single (σ k).succ (1 : ℤ) : ZV) i) j

def leftRaw (k : Fin 12) : ZEnd :=
  let p := zstandard k
  ![![p 0,-p 1,-p 2,-p 3],![p 1,p 0,p 3,-p 2],
    ![p 2,-p 3,p 0,p 1],![p 3,p 2,-p 1,p 0]]

def normalIndex (v : ZV) : Fin 12 :=
  if v 0=0 then if v 1=0 then if v 2=0 then 3 else 2 else 1
  else if v 1=0 then 0 else
    ⟨4+(if v 1=v 0 then 0 else 4)+(if v 2=v 0 then 0 else 2)+
      (if v 3=v 0 then 0 else 1),by split_ifs <;> omega⟩

def normalScale (v : ZV) : ℤ :=
  if v 0=0 then if v 1=0 then if v 2=0 then v 3 else v 2 else v 1 else v 0

def PreservesRaw (A : ZEnd) : Prop :=
  ∀ k : Fin 12, ∃ j : Fin 12, ∃ c : ℤ, c ≠ 0 ∧ A *ᵥ zstandard k = c • zstandard j

def RawCheck (A : ZEnd) : Prop := ∀ k : Fin 12,
  normalScale (A *ᵥ zstandard k) ≠ 0 ∧
    A *ᵥ zstandard k = normalScale (A *ᵥ zstandard k) •
      zstandard (normalIndex (A *ᵥ zstandard k))

instance (A : ZEnd) : Decidable (RawCheck A) := by unfold RawCheck; infer_instance

theorem checked_preserves {A : ZEnd} (h : RawCheck A) : PreservesRaw A := by
  intro k
  exact ⟨normalIndex (A *ᵥ zstandard k),normalScale (A *ᵥ zstandard k),(h k).1,(h k).2⟩

theorem signedRaw_certificate : ∀ (σ : Equiv.Perm (Fin 3)) (ε : Fin 3 → Bool),
    RawCheck (signedRaw σ ε) ∧ RawCheck (zsharp (signedRaw σ ε)) ∧
      (signedRaw σ ε).det ≠ 0 := by
  intro σ ε
  fin_cases σ <;> fin_cases ε <;> decide +kernel

theorem leftRaw_certificate : ∀ k : Fin 12,
    RawCheck (leftRaw k) ∧ RawCheck (zsharp (leftRaw k)) ∧ (leftRaw k).det ≠ 0 := by
  intro k
  fin_cases k <;> decide +kernel

end Holant.Certificates.TetrahedralPreservers
