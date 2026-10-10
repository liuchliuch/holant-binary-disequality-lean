import Holant.Certificates.IcosahedralSeparator.Arithmetic
import Holant.Certificates.IcosahedralSeparator.UniformRankThree

/-! Kernel-computable exact golden Gaussian determinants, with a proved
interpretation as the actual complex determinant. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant.Certificates.RainbowOrbit
set_option backward.isDefEq.respectTransparency false

def gsumFin : {n : ℕ} → (Fin n→GScalar) → GScalar
  | 0,_=>gz
  | n+1,f=>gadd (f 0) (gsumFin (fun i:Fin n=>f i.succ))

 theorem gembed_gsumFin {n : ℕ} (f : Fin n→GScalar) :
    gembed (gsumFin f)=∑i,gembed (f i) := by
  induction n with
  | zero=>simp [gsumFin]
  | succ n ih=>simp [gsumFin,ih,Fin.sum_univ_succ]

def gdet3 (A : Matrix (Fin 3) (Fin 3) GScalar) : GScalar :=
  gsub (gadd (gadd
    (gsub (gsub (gmul (gmul (A 0 0) (A 1 1)) (A 2 2))
      (gmul (gmul (A 0 0) (A 1 2)) (A 2 1)))
      (gmul (gmul (A 0 1) (A 1 0)) (A 2 2)))
    (gmul (gmul (A 0 1) (A 1 2)) (A 2 0)))
    (gmul (gmul (A 0 2) (A 1 0)) (A 2 1)))
    (gmul (gmul (A 0 2) (A 1 1)) (A 2 0))

 theorem gembed_gdet3 (A : Matrix (Fin 3) (Fin 3) GScalar) :
    gembed (gdet3 A)=Matrix.det (fun i j=>gembed (A i j)) := by
  rw [Matrix.det_fin_three]
  simp [gdet3]

def gdet4 (A : Matrix (Fin 4) (Fin 4) GScalar) : GScalar :=
  gsumFin fun j=>gscale ((-1:ℤ)^j.val)
    (gmul (A 0 j) (gdet3 (A.submatrix Fin.succ j.succAbove)))

 theorem gembed_gdet4 (A : Matrix (Fin 4) (Fin 4) GScalar) :
    gembed (gdet4 A)=Matrix.det (fun i j=>gembed (A i j)) := by
  rw [gdet4,gembed_gsumFin,Matrix.det_succ_row_zero]
  apply Finset.sum_congr rfl
  intro j _
  simp [gembed_gdet3,Matrix.submatrix,mul_assoc]
  left
  rfl

def pairIndex : Fin 4→Bool×Bool := ![(false,false),(false,true),(true,false),(true,true)]
noncomputable def pairEquiv : Fin 4≃Bool×Bool := Equiv.ofBijective pairIndex (by decide)

end Holant.Certificates.IcosahedralSeparator
