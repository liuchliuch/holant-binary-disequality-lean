import Holant.Certificates.AffineEndpointCounts.OrbitBatch00
import Holant.Certificates.AffineEndpointCounts.OrbitBatch01
import Holant.Certificates.AffineEndpointCounts.OrbitBatch02
import Holant.Certificates.AffineEndpointCounts.OrbitBatch03
import Holant.Certificates.AffineEndpointCounts.OrbitBatch04
import Holant.Certificates.AffineEndpointCounts.OrbitBatch05
import Holant.Certificates.AffineEndpointCounts.OrbitBatch06
import Holant.Certificates.AffineEndpointCounts.OrbitBatch07
import Holant.Certificates.AffineEndpointCounts.OrbitBatch08
import Holant.Certificates.AffineEndpointCounts.OrbitBatch09
import Holant.Certificates.AffineEndpointCounts.OrbitBatch10
import Holant.Certificates.AffineEndpointCounts.OrbitBatch11
import Holant.Certificates.AffineEndpointCounts.OrbitBatch12
import Holant.Certificates.AffineEndpointCounts.OrbitBatch13
import Holant.Certificates.AffineEndpointCounts.OrbitBatch14
import Holant.Certificates.AffineEndpointCounts.OrbitBatch15
import Holant.Certificates.AffineEndpointCounts.OrbitBatch16
import Holant.Certificates.AffineEndpointCounts.OrbitBatch17
import Holant.Certificates.AffineEndpointCounts.OrbitBatch18
import Holant.Certificates.AffineEndpointCounts.OrbitBatch19
import Holant.Certificates.AffineEndpointCounts.OrbitBatch20
import Holant.Certificates.AffineEndpointCounts.OrbitBatch21
import Holant.Certificates.AffineEndpointCounts.OrbitBatch22
import Holant.Certificates.AffineEndpointCounts.OrbitBatch23
import Holant.Certificates.AffineEndpointCounts.OrbitBatch24
import Holant.Certificates.AffineEndpointCounts.OrbitBatch25
import Holant.Certificates.AffineEndpointCounts.OrbitBatch26
import Holant.Certificates.AffineEndpointCounts.OrbitBatch27
import Holant.Certificates.AffineEndpointCounts.OrbitBatch28
import Holant.Certificates.AffineEndpointCounts.OrbitBatch29
import Holant.Certificates.AffineEndpointCounts.OrbitBatch30
import Holant.Certificates.AffineEndpointCounts.OrbitBatch31
import Holant.Certificates.AffineEndpointCounts.OrbitBatch32
import Holant.Certificates.AffineEndpointCounts.OrbitBatch33
import Holant.Certificates.AffineEndpointCounts.OrbitBatch34
import Holant.Certificates.AffineEndpointCounts.OrbitBatch35
import Holant.Certificates.AffineEndpointCounts.OrbitBatch36
import Holant.Certificates.AffineEndpointCounts.OrbitBatch37
import Holant.Certificates.AffineEndpointCounts.OrbitBatch38
namespace Holant.Certificates.AffineEndpointCounts
open Holant.Certificates.AffineEndpoint Holant.Certificates.OctahedralSeparator IntegerValues
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option maxErrors 3
 theorem orbitRowCheck_pass (r : Fin 612) : orbitRowCheck r = true := by
  have hr := r.isLt
  have hd : r.val%16 < 16 := Nat.mod_lt _ (by decide)
  have he : r.val/16*16+r.val%16=r.val := by simpa only [Nat.mul_comm] using Nat.div_add_mod r.val 16
  generalize hb : r.val/16 = b
  have hblt : b < 39 := by omega
  interval_cases b
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_00 ⟨r.val%16,hj⟩
    have harg : (⟨0+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_01 ⟨r.val%16,hj⟩
    have harg : (⟨16+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_02 ⟨r.val%16,hj⟩
    have harg : (⟨32+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_03 ⟨r.val%16,hj⟩
    have harg : (⟨48+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_04 ⟨r.val%16,hj⟩
    have harg : (⟨64+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_05 ⟨r.val%16,hj⟩
    have harg : (⟨80+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_06 ⟨r.val%16,hj⟩
    have harg : (⟨96+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_07 ⟨r.val%16,hj⟩
    have harg : (⟨112+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_08 ⟨r.val%16,hj⟩
    have harg : (⟨128+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_09 ⟨r.val%16,hj⟩
    have harg : (⟨144+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_10 ⟨r.val%16,hj⟩
    have harg : (⟨160+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_11 ⟨r.val%16,hj⟩
    have harg : (⟨176+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_12 ⟨r.val%16,hj⟩
    have harg : (⟨192+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_13 ⟨r.val%16,hj⟩
    have harg : (⟨208+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_14 ⟨r.val%16,hj⟩
    have harg : (⟨224+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_15 ⟨r.val%16,hj⟩
    have harg : (⟨240+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_16 ⟨r.val%16,hj⟩
    have harg : (⟨256+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_17 ⟨r.val%16,hj⟩
    have harg : (⟨272+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_18 ⟨r.val%16,hj⟩
    have harg : (⟨288+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_19 ⟨r.val%16,hj⟩
    have harg : (⟨304+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_20 ⟨r.val%16,hj⟩
    have harg : (⟨320+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_21 ⟨r.val%16,hj⟩
    have harg : (⟨336+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_22 ⟨r.val%16,hj⟩
    have harg : (⟨352+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_23 ⟨r.val%16,hj⟩
    have harg : (⟨368+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_24 ⟨r.val%16,hj⟩
    have harg : (⟨384+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_25 ⟨r.val%16,hj⟩
    have harg : (⟨400+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_26 ⟨r.val%16,hj⟩
    have harg : (⟨416+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_27 ⟨r.val%16,hj⟩
    have harg : (⟨432+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_28 ⟨r.val%16,hj⟩
    have harg : (⟨448+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_29 ⟨r.val%16,hj⟩
    have harg : (⟨464+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_30 ⟨r.val%16,hj⟩
    have harg : (⟨480+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_31 ⟨r.val%16,hj⟩
    have harg : (⟨496+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_32 ⟨r.val%16,hj⟩
    have harg : (⟨512+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_33 ⟨r.val%16,hj⟩
    have harg : (⟨528+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_34 ⟨r.val%16,hj⟩
    have harg : (⟨544+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_35 ⟨r.val%16,hj⟩
    have harg : (⟨560+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_36 ⟨r.val%16,hj⟩
    have harg : (⟨576+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 16 := by omega
    have h := orbit_batch_37 ⟨r.val%16,hj⟩
    have harg : (⟨592+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h
  · have hj : r.val%16 < 4 := by omega
    have h := orbit_batch_38 ⟨r.val%16,hj⟩
    have harg : (⟨608+r.val%16,by omega⟩ : Fin 612) = r := by apply Fin.ext; dsimp; omega
    simpa only [harg] using h

 theorem orbit_coefficient_check (r : Fin 612) (j : Fin 21) :
    IntegerCoefficient.mul (invariantPalette (orbitDigit r j)) (referenceInteger r 15) =
      IntegerCoefficient.mul (referenceInteger r (centralCode (invariantPair j).val.1))
        (referenceInteger r (centralCode (invariantPair j).val.2)) := by
  have h := orbitRowCheck_pass r
  exact of_decide_eq_true (List.all_eq_true.mp h j (by simp))
end Holant.Certificates.AffineEndpointCounts
