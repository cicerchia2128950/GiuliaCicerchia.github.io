import java.math.BigInteger;
import java.nio.file.*;
import java.security.MessageDigest;
import java.util.*;

/**
 * Homework 3 - toy ECC scheme (secp256k1, small private key) vs Caesar cipher, and two attacks.
 * Standard library only.  Run:  java Homework3.java      (needs corpus.txt and test.txt in the same folder)
 *
 *  A. toy hybrid EC-ElGamal scheme     B. Caesar cipher       C. statistics of the ciphertexts
 *  D. statistical attack on Caesar     E. attacks on the restricted private key
 *  F. malleability (design weakness)
 */
public class Homework3 {
    static final String MESSAGE = "MEET ME AT THE BRIDGE AT MIDNIGHT";
    static final String PROSE = ("The old lighthouse keeper climbed the spiral stairs every evening, carrying a lantern he no longer needed "
        + "because the electric light had been installed years before, yet he refused to give up the habit. From the gallery he "
        + "could see the fishing boats returning one by one, small shapes against a sky turning from orange to violet, and he "
        + "counted them out loud as if somebody might be listening. When the last one had passed the breakwater he went back down, "
        + "made a pot of strong tea, and wrote a few lines in the logbook about the weather, the tide and the colour of the sea. "
        + "On some nights a storm rolled in from the west and the windows rattled in their frames, and then he sat awake until "
        + "morning with a blanket over his knees, listening to the wind and thinking about the people who depended on that light "
        + "without ever knowing his name. Nobody had asked him to stay, but nobody had come to take his place either, so every "
        + "spring he repainted the railing, oiled the hinges of the heavy door and waited for the first fog of the year.");

    // ================= A. secp256k1 (affine, null = point at infinity) =================
    static final BigInteger P = BigInteger.TWO.pow(256).subtract(BigInteger.TWO.pow(32)).subtract(BigInteger.valueOf(977));
    static final BigInteger N = new BigInteger("FFFFFFFFFFFFFFFFFFFFFFFFFFFFFFFEBAAEDCE6AF48A03BBFD25E8CD0364141", 16);
    static final BigInteger[] G = {
        new BigInteger("79BE667EF9DCBBAC55A06295CE870B07029BFCDB2DCE28D959F2815B16F81798", 16),
        new BigInteger("483ADA7726A3C4655DA4FBFC0E1108A8FD17B448A68554199C47D08FFB10D4B8", 16)};
    static final BigInteger THREE = BigInteger.valueOf(3);

    static BigInteger[] add(BigInteger[] A, BigInteger[] B) {
        if (A == null) return B;
        if (B == null) return A;
        BigInteger l;
        if (A[0].equals(B[0])) {
            if (A[1].add(B[1]).mod(P).signum() == 0) return null;
            l = THREE.multiply(A[0]).multiply(A[0]).multiply(A[1].shiftLeft(1).mod(P).modInverse(P)).mod(P);
        } else {
            l = B[1].subtract(A[1]).multiply(B[0].subtract(A[0]).mod(P).modInverse(P)).mod(P);
        }
        BigInteger x = l.multiply(l).subtract(A[0]).subtract(B[0]).mod(P);
        return new BigInteger[]{x, l.multiply(A[0].subtract(x)).subtract(A[1]).mod(P)};
    }
    static BigInteger[] neg(BigInteger[] A) { return A == null ? null : new BigInteger[]{A[0], A[1].negate().mod(P)}; }
    static BigInteger[] mul(BigInteger k, BigInteger[] Q) {          // double-and-add
        BigInteger[] R = null;
        for (int i = 0; i < k.bitLength(); i++) {
            if (k.testBit(i)) R = add(R, Q);
            Q = add(Q, Q);
        }
        return R;
    }
    static boolean eq(BigInteger[] A, BigInteger[] B) { return A == null ? B == null : B != null && A[0].equals(B[0]) && A[1].equals(B[1]); }
    static String key(BigInteger[] A) { return A == null ? "inf" : A[0] + "," + A[1]; }
    static String hex32(BigInteger x) { return String.format("%064x", x); }

    // Toy scheme: k in [1, K_MAX] (RESTRICTED); Q = kG.  Enc: r random 256-bit, C1 = rG, S = rQ, C2 = m xor H(S.x||ctr)
    static final long K_MAX = 1L << 20;
    static byte[] keystream(BigInteger[] S, int n) throws Exception {
        byte[] out = new byte[n];
        byte[] sx = S[0].toByteArray();                       // fixed 32-byte big-endian encoding of S.x
        byte[] seed = new byte[32];
        for (int i = 0; i < Math.min(32, sx.length); i++) seed[31 - i] = sx[sx.length - 1 - i];
        MessageDigest md = MessageDigest.getInstance("SHA-256");
        int o = 0, ctr = 0;
        while (o < n) {
            md.update(seed);
            md.update(new byte[]{(byte) (ctr >>> 24), (byte) (ctr >>> 16), (byte) (ctr >>> 8), (byte) ctr});
            ctr++;
            byte[] h = md.digest();
            for (int i = 0; i < 32 && o < n; i++) out[o++] = h[i];
        }
        return out;
    }
    static byte[] xor(byte[] a, byte[] b) { byte[] r = new byte[a.length]; for (int i = 0; i < a.length; i++) r[i] = (byte) (a[i] ^ b[i]); return r; }
    static String hex(byte[] b) { StringBuilder s = new StringBuilder(); for (byte x : b) s.append(String.format("%02x", x)); return s.toString(); }
    static BigInteger randBelow(BigInteger n, Random rnd) { BigInteger r; do { r = new BigInteger(n.bitLength(), rnd); } while (r.signum() == 0 || r.compareTo(n) >= 0); return r; }

    static BigInteger[][] encrypt(BigInteger[] Q, byte[] msg, Random rnd, byte[][] outC2) throws Exception {
        BigInteger r = randBelow(N, rnd);
        BigInteger[] C1 = mul(r, G), S = mul(r, Q);
        outC2[0] = xor(msg, keystream(S, msg.length));
        return new BigInteger[][]{C1};
    }
    static byte[] decrypt(BigInteger k, BigInteger[] C1, byte[] C2) throws Exception {
        return xor(C2, keystream(mul(k, C1), C2.length));
    }

    // ================= B. Caesar (letters only, a-z as 0..25) =================
    static String caesar(String t, int k) {
        StringBuilder s = new StringBuilder();
        for (char c : t.toCharArray()) {
            if (c >= 'A' && c <= 'Z') s.append((char) ((c - 'A' + k % 26 + 26) % 26 + 'A'));
            else if (c >= 'a' && c <= 'z') s.append((char) ((c - 'a' + k % 26 + 26) % 26 + 'a'));
            else s.append(c);
        }
        return s.toString();
    }
    static String lettersOnly(String t) { return t.toLowerCase().replaceAll("[^a-z]", ""); }
    static int[] toIdx(String t) { int[] a = new int[t.length()]; for (int i = 0; i < a.length; i++) a[i] = t.charAt(i) - 'a'; return a; }
    static int[] shiftBy(int[] c, int k, int[] w) { for (int i = 0; i < c.length; i++) w[i] = ((c[i] - k) % 26 + 26) % 26; return w; }

    // ================= C. statistics =================
    static double entropy(int[] counts, int n) { double h = 0; for (int c : counts) if (c > 0) { double p = (double) c / n; h -= p * Math.log(p) / Math.log(2); } return h; }
    static double ic(int[] counts, int n) { double s = 0; for (int c : counts) s += (double) c * (c - 1); return s / ((double) n * (n - 1)); }

    // ================= D. language model and scorers =================
    static double[] p1 = new double[26], lp1 = new double[26];
    static int[][] c2 = new int[26][26]; static int[] x2 = new int[26];
    static int[][][] c3 = new int[26][26][26]; static int[][] x3 = new int[26][26];
    static void train(String corpus) {
        int[] a = toIdx(corpus); long[] u = new long[26];
        for (int v : a) u[v]++;
        for (int i = 0; i < 26; i++) { p1[i] = (double) u[i] / a.length; lp1[i] = Math.log(p1[i]); }
        for (int i = 0; i + 1 < a.length; i++) { c2[a[i]][a[i + 1]]++; x2[a[i]]++; }
        for (int i = 0; i + 2 < a.length; i++) { c3[a[i]][a[i + 1]][a[i + 2]]++; x3[a[i]][a[i + 1]]++; }
    }
    static final String[] NAMES = {"peak=e", "chi-square", "unigram LL", "bigram LL", "trigram LL"};
    static double score(int m, int[] c, int k, int[] w) {
        shiftBy(c, k, w); int n = c.length; double s = 0;
        switch (m) {
            case 1: { int[] cnt = new int[26]; for (int v : w) cnt[v]++;
                for (int i = 0; i < 26; i++) { double e = n * p1[i]; s -= (cnt[i] - e) * (cnt[i] - e) / e; } return s; }
            case 2: for (int v : w) s += lp1[v]; return s;
            case 3: for (int i = 0; i + 1 < n; i++) s += Math.log((c2[w[i]][w[i + 1]] + .5) / (x2[w[i]] + 13)); return s;
            default: for (int i = 0; i + 2 < n; i++) s += Math.log((c3[w[i]][w[i + 1]][w[i + 2]] + .5) / (x3[w[i]][w[i + 1]] + 13)); return s;
        }
    }
    static int attack(int m, int[] c) {
        if (m == 0) {                                          // most frequent cipher letter is assumed to be 'e'
            int[] cnt = new int[26]; for (int v : c) cnt[v]++;
            int max = 0; for (int v : cnt) max = Math.max(max, v);
            int best = 0; for (int v : c) if (cnt[v] == max) { best = v; break; }   // ties: first letter seen in the ciphertext
            return ((best - 4) % 26 + 26) % 26;
        }
        int[] w = new int[c.length]; int bk = 0; double bs = -1e300;
        for (int k = 0; k < 26; k++) { double s = score(m, c, k, w); if (s > bs) { bs = s; bk = k; } }
        return bk;
    }
    static void experiment(String title, String text, int[] lengths, int trials, Random rnd) {
        System.out.println(title);
        System.out.print("  length |"); for (String n : NAMES) System.out.printf(" %10s |", n); System.out.println();
        int[] t = toIdx(text);
        for (int L : lengths) {
            int[] wins = new int[5];
            for (int tr = 0; tr < trials; tr++) {
                int i = rnd.nextInt(t.length - L), key = 1 + rnd.nextInt(25);
                int[] c = new int[L]; for (int j = 0; j < L; j++) c[j] = (t[i + j] + key) % 26;
                for (int m = 0; m < 5; m++) if (attack(m, c) == key) wins[m]++;
            }
            System.out.printf("  %6d |", L); for (int m = 0; m < 5; m++) System.out.printf(" %9.1f%% |", 100.0 * wins[m] / trials); System.out.println();
        }
    }

    // ================= E. attacks on the small private key =================
    static BigInteger bruteForce(BigInteger[] Q, long kmax) {
        BigInteger[] R = G; long k = 1;
        while (!eq(R, Q) && k < kmax) { R = add(R, G); k++; }
        return eq(R, Q) ? BigInteger.valueOf(k) : null;
    }
    static BigInteger bsgs(BigInteger[] Q, long kmax, long[] mOut) {
        long m = (long) Math.sqrt((double) kmax) + 1; mOut[0] = m;
        HashMap<String, Long> baby = new HashMap<>(); baby.put("inf", 0L);
        BigInteger[] R = null;
        for (long j = 1; j < m; j++) { R = add(R, G); baby.put(key(R), j); }
        BigInteger[] step = neg(mul(BigInteger.valueOf(m), G)); R = Q;
        for (long i = 0; i <= m; i++) {
            Long j = baby.get(key(R));
            if (j != null) { BigInteger k = BigInteger.valueOf(i * m + j); if (k.signum() > 0 && eq(mul(k, G), Q)) return k; }
            R = add(R, step);
        }
        return null;
    }
    static String human(double s) {
        if (s < 1) return String.format("%.1f ms", s * 1e3);
        if (s < 60) return String.format("%.1f s", s);
        if (s < 3600) return String.format("%.1f min", s / 60);
        if (s < 86400) return String.format("%.1f h", s / 3600);
        if (s < 3.15e7) return String.format("%.1f days", s / 86400);
        return String.format("%.2e years", s / 3.15e7);
    }
    static String line() { return "=".repeat(72); }

    public static void main(String[] args) throws Exception {
        Random rnd = new Random(2026);                       // fixed seed -> reproducible
        String dir = args.length > 0 ? args[0] : ".";
        // ---------------- A ----------------
        System.out.println(line() + "\nA. TOY ECC SCHEME ON secp256k1  (private key restricted to [1, 2^20])\n" + line());
        BigInteger k = BigInteger.valueOf(1 + (long) (rnd.nextDouble() * K_MAX));
        BigInteger[] Q = mul(k, G);
        System.out.println("private key k   = " + k + "   (secret, " + k.bitLength() + " bits used out of 256)");
        System.out.println("public key  Q.x = " + hex32(Q[0]) + "\n            Q.y = " + hex32(Q[1]));
        byte[] msg = MESSAGE.getBytes("UTF-8"); byte[][] c2out = new byte[1][];
        BigInteger[] C1 = encrypt(Q, msg, rnd, c2out)[0]; byte[] C2 = c2out[0];
        System.out.println("plaintext       = " + MESSAGE + "\nC1 = r*G  .x    = " + hex32(C1[0]) + "\nC2 (ciphertext) = " + hex(C2));
        System.out.println("decrypted       = " + new String(decrypt(k, C1, C2), "UTF-8") + "   -> " + (Arrays.equals(decrypt(k, C1, C2), msg) ? "OK" : "FAIL"));
        System.out.println("with key k+1    = " + hex(decrypt(k.add(BigInteger.ONE), C1, C2)).substring(0, 40) + "... (garbage)");
        // ---------------- B ----------------
        System.out.println("\n" + line() + "\nB. CAESAR CIPHER\n" + line());
        String cc = caesar(MESSAGE, 7);
        System.out.println("key = 7\nplaintext  = " + MESSAGE + "\nciphertext = " + cc + "\ndecrypted  = " + caesar(cc, -7));
        // ---------------- C ----------------
        System.out.println("\n" + line() + "\nC. STATISTICAL PROPERTIES OF THE TWO CIPHERTEXTS (4000-character English text)\n" + line());
        StringBuilder sb = new StringBuilder(); while (sb.length() < 4000) sb.append(PROSE);
        String longPlain = sb.substring(0, 4000), longCaes = caesar(longPlain, 11);
        byte[][] eo = new byte[1][]; encrypt(Q, longPlain.getBytes("UTF-8"), rnd, eo); byte[] eccLong = eo[0];
        int[] cp = new int[26], cc2 = new int[26], cb = new int[256];
        for (int v : toIdx(lettersOnly(longPlain))) cp[v]++;
        for (int v : toIdx(lettersOnly(longCaes))) cc2[v]++;
        for (byte b : eccLong) cb[b & 0xff]++;
        int nl = lettersOnly(longPlain).length();
        System.out.printf("%-32s%12s%12s%15s%n", "", "plaintext", "Caesar ct", "ECC-hybrid ct");
        System.out.printf("%-32s%12.3f%12.3f%15.3f   (bits/symbol)%n", "entropy of letter/byte distr.", entropy(cp, nl), entropy(cc2, nl), entropy(cb, eccLong.length));
        System.out.printf("%-32s%12.4f%12.4f%15.4f%n", "index of coincidence", ic(cp, nl), ic(cc2, nl), ic(cb, eccLong.length));
        int[] sp = cp.clone(), sc = cc2.clone(); Arrays.sort(sp); Arrays.sort(sc);
        System.out.println("   (English ~0.066, uniform 26 letters = 0.0385, uniform 256 bytes = 0.0039)");
        System.out.println("   sorted letter counts identical for plaintext and Caesar ct: " + Arrays.equals(sp, sc));
        // ---------------- D ----------------
        System.out.println("\n" + line() + "\nD. STATISTICAL CRYPTANALYSIS OF THE CAESAR CIPHER\n" + line());
        String corpus = lettersOnly(new String(Files.readAllBytes(Paths.get(dir, "corpus.txt")), "UTF-8"));
        String legal = lettersOnly(new String(Files.readAllBytes(Paths.get(dir, "test.txt")), "UTF-8"));
        train(corpus);
        System.out.println("training corpus: " + corpus.length() + " letters (English prose)");
        Integer[] ord = new Integer[26]; for (int i = 0; i < 26; i++) ord[i] = i;
        Arrays.sort(ord, (a, b) -> Double.compare(p1[b], p1[a]));
        StringBuilder top = new StringBuilder(); for (int i = 0; i < 8; i++) top.append(String.format("%c:%.1f%% ", 'a' + ord[i], 100 * p1[ord[i]]));
        System.out.println("most frequent letters: " + top);
        int[] ex = toIdx(lettersOnly(cc));
        System.out.println("\nWorked example on the short message (" + ex.length + " letters): ciphertext = " + cc);
        for (int m = 0; m < 5; m++) System.out.printf("   %-11s -> key %d%n", NAMES[m], attack(m, ex));
        int[] lengths = {5, 10, 20, 40, 80, 160, 320};
        System.out.println();
        experiment("Success rate, 400 random (window, key) pairs per length, test text = legal English (licenses):", legal, lengths, 400, rnd);
        System.out.println();
        experiment("Same, test text = narrative prose (own passage, ~900 letters, windows overlap):", lettersOnly(PROSE), lengths, 400, rnd);
        System.out.println("\nRank of the TRUE key under bigram LL for very short ciphertexts (200 trials):");
        int[] lt = toIdx(legal);
        for (int L : new int[]{3, 5, 8}) {
            double sum = 0; int first = 0;
            for (int tr = 0; tr < 200; tr++) {
                int i = rnd.nextInt(lt.length - L), key = 1 + rnd.nextInt(25);
                int[] c = new int[L]; for (int j = 0; j < L; j++) c[j] = (lt[i + j] + key) % 26;
                int[] w = new int[L]; double ts = score(3, c, key, w); int rank = 1;
                for (int kk = 0; kk < 26; kk++) if (kk != key && score(3, c, kk, new int[L]) > ts) rank++;
                sum += rank; if (rank == 1) first++;
            }
            System.out.printf("   L=%d: mean rank %.2f, true key ranked first %d%%%n", L, sum / 200, first * 100 / 200);
        }
        int bad = 0;
        for (int tr = 0; tr < 200; tr++) {
            int key = 1 + rnd.nextInt(25); int[] c = new int[200]; for (int j = 0; j < 200; j++) c[j] = (rnd.nextInt(26) + key) % 26;
            if (attack(1, c) == key) bad++;
        }
        System.out.printf("%nLimitation: chi-square success on uniformly random 'plaintext' (200 letters): %.1f%%  (chance = 3.8%%)%n", bad / 2.0);
        // ---------------- E ----------------
        System.out.println("\n" + line() + "\nE. ATTACK ON THE RESTRICTED PRIVATE KEY  (we only use Q and the group law)\n" + line());
        BigInteger[] R = G; for (int i = 0; i < 40000; i++) R = add(R, G);         // warm-up (JIT)
        long t0 = System.nanoTime(); R = G; for (int i = 0; i < 40000; i++) R = add(R, G);
        double tAdd = (System.nanoTime() - t0) / 40000.0 / 1e9;
        System.out.printf("cost of one affine point addition: %.1f microseconds%n", tAdd * 1e6);
        for (int bits : new int[]{12, 16}) {
            long kk = (1L << bits) - 5; t0 = System.nanoTime();
            BigInteger f = bruteForce(mul(BigInteger.valueOf(kk), G), 1L << bits);
            System.out.printf("brute force, k in [1,2^%d]  : found %s (true %d) in %.3fs  (%d additions)%n", bits, f, kk, (System.nanoTime() - t0) / 1e9, kk);
        }
        for (int bits : new int[]{16, 20, 24, 32}) {
            long kk = 1 + (long) (rnd.nextDouble() * (1L << bits)); long[] m = new long[1]; t0 = System.nanoTime();
            BigInteger f = bsgs(mul(BigInteger.valueOf(kk), G), 1L << bits, m);
            System.out.printf("BSGS,        k in [1,2^%d]: found %s (true %d) %s  m=%d, %.2fs, table=%d points%n", bits, f, kk, f != null && f.longValue() == kk ? "OK" : "FAIL", m[0], (System.nanoTime() - t0) / 1e9, m[0]);
        }
        System.out.println("\nAttack on the scheme of section A (attacker sees only Q, C1, C2):");
        long[] m = new long[1]; t0 = System.nanoTime(); BigInteger kf = bsgs(Q, K_MAX, m);
        System.out.printf("   recovered private key = %s  (true %s) in %.2fs%n", kf, k, (System.nanoTime() - t0) / 1e9);
        System.out.println("   decrypted message     = " + new String(decrypt(kf, C1, C2), "UTF-8"));
        System.out.println("\nExtrapolated cost (1 group op = measured time above, ignoring memory):");
        System.out.printf("   %8s | %22s | %26s | BSGS memory (points)%n", "key bits", "brute force K/2 ops", "BSGS ~2*sqrt(K) ops");
        for (int bits : new int[]{20, 32, 40, 64, 128, 256}) {
            double K = Math.pow(2, bits);
            System.out.printf("   %8d | %22s | %26s | 2^%d%n", bits, human(K * tAdd / 2), human(2 * Math.sqrt(K) * tAdd), bits / 2);
        }
        // ---------------- F ----------------
        System.out.println("\n" + line() + "\nF. DESIGN WEAKNESS INDEPENDENT OF KEY SIZE: MALLEABILITY (no authentication)\n" + line());
        byte[] forged = C2.clone(); byte[] old = "MIDNIGHT".getBytes(), neu = "NOON TIM".getBytes(); int pos = MESSAGE.indexOf("MIDNIGHT");
        for (int i = 0; i < old.length; i++) forged[pos + i] ^= old[i] ^ neu[i];
        System.out.println("attacker knows part of the plaintext, never the key, and edits the ciphertext:");
        System.out.println("   decrypted forged ciphertext: " + new String(decrypt(k, C1, forged), "UTF-8"));
    }
}
