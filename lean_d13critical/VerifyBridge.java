import java.math.BigInteger;

/** Independent exact checker for the Round-25 bridge equations. */
public final class VerifyBridge {
  private static final BigInteger TEN = BigInteger.TEN;
  private static final BigInteger ONE = BigInteger.ONE;

  private static void check(int p, int e, int digits, int d, int c) {
    BigInteger P = BigInteger.valueOf(p);
    BigInteger D = BigInteger.valueOf(d);
    BigInteger C = BigInteger.valueOf(c);
    BigInteger numerator = C.multiply(TEN.pow(digits)).add(ONE);
    BigInteger[] qr = numerator.divideAndRemainder(D);
    if (qr[1].signum() != 0) throw new AssertionError("nonintegral quotient");
    BigInteger q = qr[0];
    if (!P.pow(e).subtract(TEN).equals(D)) throw new AssertionError("wrong D");
    if (!BigInteger.TEN.multiply(BigInteger.TEN.multiply(P).add(BigInteger.valueOf(e))).equals(C))
      throw new AssertionError("wrong C");
    if (q.toString().length() != digits) throw new AssertionError("wrong digits");
    if (!D.multiply(q).equals(numerator)) throw new AssertionError("bridge equation");

    BigInteger wrongDigits = C.multiply(TEN.pow(digits - 1)).add(ONE);
    if (D.multiply(q).equals(wrongDigits)) throw new AssertionError("digit mutation accepted");
    int reversed = 10 * (10 * e + p);
    BigInteger wrongOrder = BigInteger.valueOf(reversed).multiply(TEN.pow(digits)).add(ONE);
    if (D.multiply(q).equals(wrongOrder)) throw new AssertionError("order mutation accepted");
  }

  public static void main(String[] args) {
    check(7, 4, 733, 2391, 740);
    check(3, 7, 666, 2177, 370);
    System.out.println("JAVA_BRIDGE_CHECK_PASS cases=2 mutations=4");
  }
}
