import Holant.Certificates.PlatonicBridgeInterface.FivePointData
namespace Holant.Certificates.PlatonicBridgeInterface
open Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem five_product_row_0 : ∀ h x, fiveAction (icosahedralProductIndex 0 h) x = fiveAction 0 (fiveAction h x) := by decide +kernel

theorem five_product_row_1 : ∀ h x, fiveAction (icosahedralProductIndex 1 h) x = fiveAction 1 (fiveAction h x) := by decide +kernel

theorem five_product_row_2 : ∀ h x, fiveAction (icosahedralProductIndex 2 h) x = fiveAction 2 (fiveAction h x) := by decide +kernel

theorem five_product_row_3 : ∀ h x, fiveAction (icosahedralProductIndex 3 h) x = fiveAction 3 (fiveAction h x) := by decide +kernel

theorem five_product_row_4 : ∀ h x, fiveAction (icosahedralProductIndex 4 h) x = fiveAction 4 (fiveAction h x) := by decide +kernel

theorem five_product_row_5 : ∀ h x, fiveAction (icosahedralProductIndex 5 h) x = fiveAction 5 (fiveAction h x) := by decide +kernel

theorem five_product_row_6 : ∀ h x, fiveAction (icosahedralProductIndex 6 h) x = fiveAction 6 (fiveAction h x) := by decide +kernel

theorem five_product_row_7 : ∀ h x, fiveAction (icosahedralProductIndex 7 h) x = fiveAction 7 (fiveAction h x) := by decide +kernel

theorem five_product_row_8 : ∀ h x, fiveAction (icosahedralProductIndex 8 h) x = fiveAction 8 (fiveAction h x) := by decide +kernel

theorem five_product_row_9 : ∀ h x, fiveAction (icosahedralProductIndex 9 h) x = fiveAction 9 (fiveAction h x) := by decide +kernel

end Holant.Certificates.PlatonicBridgeInterface
