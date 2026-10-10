import Holant.Certificates.IcosahedralSeparator.UniformWitnessData

namespace Holant.Certificates.IcosahedralSeparator

def UniformRankCheck (i : Fin 30) : Prop := ∀k : Fin 3,
  gdet4 (fun a b=>flatCode i k (pairIndex a) (pairIndex b))=gz ∧
  gdet3 (fun a b=>flatCode i k (pairIndex (uniformRankRows i k a))
    (pairIndex (uniformRankCols i k b)))≠gz

instance (i : Fin 30) : Decidable (UniformRankCheck i) := by unfold UniformRankCheck;infer_instance

def binaryDetCode (i : Fin 30) : GScalar:=
  gsub (gmul (binaryCode i false false) (binaryCode i true true))
    (gmul (binaryCode i false true) (binaryCode i true false))

def UniformOutsideCheck (i : Fin 30) : Prop := binaryDetCode i≠gz ∧ ∀k : Fin 60,
  let a:=pairIndex (outsideFirst i k)
  let b:=pairIndex (outsideSecond i k)
  gsub (gmul (transferCode i a.1 a.2) (groupCode k b.1 b.2))
    (gmul (transferCode i b.1 b.2) (groupCode k a.1 a.2))≠gz

instance (i : Fin 30) : Decidable (UniformOutsideCheck i) := by unfold UniformOutsideCheck;infer_instance

end Holant.Certificates.IcosahedralSeparator
