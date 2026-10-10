import Holant.Certificates.OctahedralSeparator.BaseCache

namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

abbrev PairIndex := Bool × Bool
def scalarFlatten (r : Fin 3) (t : Signature Scalar 4) : Matrix PairIndex PairIndex Scalar :=
  ![fun a b => t ![a.1,a.2,b.1,b.2],fun a b => t ![a.1,b.1,a.2,b.2],fun a b => t ![a.1,b.1,b.2,a.2]] r
def rankRows : Fin 9 → Fin 3 → Bool → PairIndex :=
  ![![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (true,true) else (false,false)),(fun b => if b then (true,false) else (false,true)),(fun b => if b then (true,false) else (false,true))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))]]
def rankCols : Fin 9 → Fin 3 → Bool → PairIndex :=
  ![![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (true,true) else (false,false)),(fun b => if b then (true,false) else (false,true)),(fun b => if b then (true,false) else (false,true))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))],![(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false)),(fun b => if b then (false,true) else (false,false))]]
def scalarMinor (M : Matrix PairIndex PairIndex Scalar) (r c : Bool → PairIndex) : Scalar :=
  M (r false) (c false)*M (r true) (c true)-M (r false) (c true)*M (r true) (c false)
def RankCertificate (M : Matrix PairIndex PairIndex Scalar) (r c : Bool → PairIndex) : Prop :=
  scalarMinor M r c ≠ 0 ∧ ∀ a b,
    scalarMinor M r c*M a b =
      (M a (c false)*M (r true) (c true)-M a (c true)*M (r true) (c false))*M (r false) b+
      (M (r false) (c false)*M a (c true)-M (r false) (c true)*M a (c false))*M (r true) b
instance (M : Matrix PairIndex PairIndex Scalar) (r c : Bool → PairIndex) : Decidable (RankCertificate M r c) := by
  unfold RankCertificate
  infer_instance
theorem rankCertificate_0 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 0)) (rankRows 0 k) (rankCols 0 k) := by decide +kernel
theorem rankCertificate_1 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 1)) (rankRows 1 k) (rankCols 1 k) := by decide +kernel
theorem rankCertificate_2 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 2)) (rankRows 2 k) (rankCols 2 k) := by decide +kernel
theorem rankCertificate_3 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 3)) (rankRows 3 k) (rankCols 3 k) := by decide +kernel
theorem rankCertificate_4 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 4)) (rankRows 4 k) (rankCols 4 k) := by decide +kernel
theorem rankCertificate_5 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 5)) (rankRows 5 k) (rankCols 5 k) := by decide +kernel
theorem rankCertificate_6 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 6)) (rankRows 6 k) (rankCols 6 k) := by decide +kernel
theorem rankCertificate_7 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 7)) (rankRows 7 k) (rankCols 7 k) := by decide +kernel
theorem rankCertificate_8 : ∀ k : Fin 3, RankCertificate (scalarFlatten k (cachedBase 8)) (rankRows 8 k) (rankCols 8 k) := by decide +kernel
theorem rankCertificates (r : Fin 9) (k : Fin 3) : RankCertificate (scalarFlatten k (cachedBase (Fin.castAdd 6 r))) (rankRows r k) (rankCols r k) := by
  fin_cases r
  · exact rankCertificate_0 k
  · exact rankCertificate_1 k
  · exact rankCertificate_2 k
  · exact rankCertificate_3 k
  · exact rankCertificate_4 k
  · exact rankCertificate_5 k
  · exact rankCertificate_6 k
  · exact rankCertificate_7 k
  · exact rankCertificate_8 k
end Holant.Certificates.OctahedralSeparator
