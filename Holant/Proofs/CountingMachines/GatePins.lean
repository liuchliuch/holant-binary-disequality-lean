import Holant.Signature
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.Gates
open Holant
def pin {K : Type*} [Zero K] [One K] (b : Bool) : Signature K 1 :=
  fun x => if x 0 = b then 1 else 0
end Holant.LocalDrafts.RemoteWork.CountingBridge.Gates
