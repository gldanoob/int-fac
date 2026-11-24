import Std

namespace Secant

variable (k b c j n : Int)

def D := 4 * k^2 * c - b^2
def lam := 2 * k * j - b * n
def U := c * n^2 - j^2
def V := n * lam k b j n
def L := k * (j^2 + c * n^2) - b * j * n
def S := 2 * k^2 * U c j n + b * V k b j n

theorem two_k_L_sub_S : 2 * k * L k b c j n - S k b c j n = (lam k b j n)^2 := by
  simp only [L, S, U, V, lam]
  grind

theorem two_k_L_add_S : 2 * k * L k b c j n + S k b c j n = D k b c * n^2 := by
  simp only [L, S, U, V, lam, D]
  grind

theorem conic_identity :
    k^2 * (U c j n)^2 + b * U c j n * V k b j n + c * (V k b j n)^2 = (L k b c j n)^2 := by
  simp only [U, V, lam, L]
  grind

end Secant
