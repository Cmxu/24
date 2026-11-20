// Solver for the "24 game" variant in 24.py: combine every card exactly once with + - * /
// to hit the goal. Usage: solve24 CARD... GOAL   (or no args: one game per stdin line,
// answered as they arrive; or `-j THREADS`: the same, solved in parallel after reading them all)
//
// Method: search backward from the goal. The last operation splits the cards into two groups
// A and B with goal = a op b, so for every value `a` the smaller group can make, the six
// values `b` that would finish the job are looked up in what B can make. Groups of up to
// SMALL cards have their full value set built once per distinct multiset of cards and kept
// for the whole process; bigger groups are answered by recursing with `b` as the new goal.
use std::collections::{HashMap, HashSet};
use std::hash::{BuildHasherDefault, Hasher};
use std::io::BufRead;
use std::rc::Rc;

type R = (i64, i64); // exact non-negative rational: (numerator, denominator)
const NONE: R = (-1, 1); // "no such operand"; skipped like every other negative value
const SMALL: u32 = 4;

fn r(n: i64, d: i64) -> R {
    let (mut a, mut b) = (n, d);
    while b != 0 {
        (a, b) = (b, a % b);
    }
    (n / a.abs(), d / a.abs()) // d > 0 stays > 0, so the sign lives in the numerator
}

// `a op b`, not reduced.
fn raw(a: R, b: R, op: char) -> R {
    match op {
        '+' => (a.0 * b.1 + b.0 * a.1, a.1 * b.1),
        '-' => (a.0 * b.1 - b.0 * a.1, a.1 * b.1),
        '*' => (a.0 * b.0, a.1 * b.1),
        _ => (a.0 * b.1, a.1 * b.0),
    }
}

// A set of rationals, stored as they come (not reduced), so that neither `insert` nor `contains`
// needs a gcd (the gcd was most of the run time): open addressing, hashed on the f64 quotient,
// compared by cross-multiplication. The f64 is only a hash; its rounding cannot cause a wrong answer.
struct Set {
    vals: Vec<R>,   // distinct, in insertion order
    slots: Vec<R>,  // power-of-two table at most half full; denominator 0 marks an empty slot
    bits: Vec<u64>, // 8 bits per slot, set where a value hashes: most misses stop here, in cache
}

impl Set {
    fn new() -> Set {
        Set { vals: vec![], slots: vec![(0, 0); 2], bits: vec![0] }
    }

    // Hash of `v` as a bit number; its slot is that / 8.
    fn bit(&self, mut v: R) -> usize {
        // Equal rationals must hash alike: n / d is correctly rounded, so it depends only on the
        // value as long as both convert to f64 exactly. Past 2^53 fall back to the reduced form.
        if (v.0 | v.1) >> 53 != 0 {
            v = r(v.0, v.1);
        }
        // top bits of the product: an f64 holding a small integer has all its entropy up there
        let h = (v.0 as f64 / v.1 as f64).to_bits().wrapping_mul(0x9e37_79b9_7f4a_7c15);
        (h >> (61 - self.slots.len().trailing_zeros())) as usize
    }

    fn contains(&self, v: R) -> bool {
        let bit = self.bit(v);
        let mut i = bit >> 3;
        if self.bits[bit >> 6] >> (bit & 63) & 1 == 0 {
            return false;
        }
        loop {
            let w = self.slots[i];
            if w.1 == 0 || v.0 as i128 * w.1 as i128 == w.0 as i128 * v.1 as i128 {
                return w.1 != 0;
            }
            i = (i + 1) & (self.slots.len() - 1);
        }
    }

    fn place(&mut self, v: R) {
        let bit = self.bit(v);
        self.bits[bit >> 6] |= 1 << (bit & 63);
        let mut i = bit >> 3;
        while self.slots[i].1 != 0 {
            i = (i + 1) & (self.slots.len() - 1);
        }
        self.slots[i] = v;
    }

    fn insert(&mut self, v: R) {
        if self.contains(v) {
            return;
        }
        self.vals.push(v);
        if 2 * self.vals.len() <= self.slots.len() {
            return self.place(v);
        }
        self.slots = vec![(0, 0); 2 * self.slots.len()];
        self.bits = vec![0; self.slots.len().div_ceil(8)];
        for i in 0..self.vals.len() {
            self.place(self.vals[i]);
        }
    }
}

// Multiply-rotate hash (the FxHash recipe) for the remaining std maps, whose keys are small integers.
#[derive(Default)]
struct Fx(u64);
impl Hasher for Fx {
    fn write(&mut self, bytes: &[u8]) {
        for c in bytes.chunks(8) {
            let mut w = [0; 8];
            w[..c.len()].copy_from_slice(c);
            self.write_u64(u64::from_ne_bytes(w));
        }
    }
    fn write_u64(&mut self, x: u64) {
        self.0 = (self.0.rotate_left(5) ^ x).wrapping_mul(0x517c_c1b7_2722_0a95);
    }
    fn finish(&self) -> u64 {
        self.0.rotate_left(26) // the good bits are the high ones; hashbrown indexes with the low ones
    }
}
type Fxb = BuildHasherDefault<Fx>;

#[derive(Default)]
struct Solver {
    all: HashMap<Vec<i64>, Rc<Set>, Fxb>, // sorted cards -> every value >= 0 they can make; kept across games
    cards: Vec<i64>,                      // this game's cards, sorted; groups are bitmasks over it
    eq: u64,                              // bit i: cards[i] == cards[i - 1]
    sets: HashMap<u64, Rc<Set>, Fxb>,     // this game's view of `all`, by mask
    dead: HashSet<(u64, R), Fxb>,         // (group bigger than SMALL, target) known to fail
}

impl Solver {
    fn build(&mut self, key: &[i64]) -> Rc<Set> {
        if let Some(s) = self.all.get(key) {
            return s.clone();
        }
        let mut out = Set::new();
        if key.len() == 1 {
            out.insert((key[0], 1));
        }
        // every split into two groups once: the first card stays on the `a` side
        for m in (1..(1u64 << key.len()) - 1).step_by(2) {
            let side = |want| (0..key.len()).filter(|&i| m >> i & 1 == want).map(|i| key[i]).collect::<Vec<_>>();
            let (sa, sb) = (self.build(&side(1)), self.build(&side(0)));
            for &x in &sa.vals {
                for &y in &sb.vals {
                    // ponytail: negative values are never formed. Complete for goal >= 0 (any
                    // expression can be rewritten with every subexpression >= 0 by flipping
                    // subtractions), but it is why negative goals are rejected in `run`.
                    let d = raw(x, y, '-');
                    for v in [raw(x, y, '+'), raw(x, y, '*'), (d.0.abs(), d.1)] {
                        out.insert(v);
                    }
                    if y.0 != 0 {
                        out.insert(raw(x, y, '/'));
                    }
                    if x.0 != 0 {
                        out.insert(raw(y, x, '/'));
                    }
                }
            }
        }
        let out = Rc::new(out);
        self.all.insert(key.to_vec(), out.clone());
        out
    }

    fn vals(&mut self, m: u64) -> Rc<Set> {
        if let Some(s) = self.sets.get(&m) {
            return s.clone();
        }
        let key: Vec<i64> = (0..self.cards.len()).filter(|&i| m >> i & 1 == 1).map(|i| self.cards[i]).collect();
        let s = self.build(&key);
        self.sets.insert(m, s.clone());
        s
    }

    // Equal cards are interchangeable: move each run of equal cards in `m` to its lowest positions.
    fn canon(&self, m: u64) -> u64 {
        let (mut out, mut i) = (0, 0);
        while i < self.cards.len() {
            let j = (i + 1..self.cards.len()).find(|&j| self.eq >> j & 1 == 0).unwrap_or(self.cards.len());
            out |= ((1u64 << (m >> i & ((1 << (j - i)) - 1)).count_ones()) - 1) << i;
            i = j;
        }
        out
    }

    // An expression over exactly the cards in `s` (a canonical mask) with value `t`, if any.
    fn find(&mut self, s: u64, t: R) -> Option<String> {
        let (n, t) = (s.count_ones(), r(t.0, t.1));
        if n == 1 {
            let c = self.cards[s.trailing_zeros() as usize];
            return ((c, 1) == t).then(|| c.to_string());
        }
        if if n <= SMALL { !self.vals(s).contains(t) } else { self.dead.contains(&(s, t)) } {
            return None;
        }
        // biggest `a` side first: those splits are the likeliest to be answered by lookups alone
        for k in (1..=n / 2).rev() {
            let mut a = s;
            loop {
                a = (a - 1) & s;
                if a == 0 {
                    break;
                }
                // skip: wrong size; the mirror image of an even split; a group that differs
                // from an earlier one only in which of several equal cards it takes
                if a.count_ones() != k || (2 * k == n && a & s & s.wrapping_neg() == 0) || (a & self.eq) >> 1 & s & !a != 0 {
                    continue;
                }
                let b = self.canon(s ^ a);
                let (sa, sb) = (self.vals(a), (n - k <= SMALL).then(|| self.vals(b)));
                for &x in &sa.vals {
                    let zero = x.0 == 0;
                    // (y, op, y goes first): the y that makes `x op y` (or `y op x`) equal t
                    let tries = [
                        (raw(t, x, '-'), '+', false),
                        (raw(x, t, '-'), '-', false),
                        (raw(t, x, '+'), '-', true),
                        // 0 * anything = 0: the plain sum of B's cards will do
                        (if !zero { raw(t, x, '/') } else if t.0 == 0 { ((0..64).filter(|i| b >> i & 1 == 1).map(|i| self.cards[i]).sum(), 1) } else { NONE }, '*', false),
                        (if zero || t.0 == 0 { NONE } else { raw(x, t, '/') }, '/', false),
                        (if zero { NONE } else { raw(t, x, '*') }, '/', true),
                    ];
                    for (y, op, y_first) in tries {
                        if y.0 < 0 || sb.as_ref().is_some_and(|sb| !sb.contains(y)) {
                            continue;
                        }
                        let Some(q) = self.find(b, y) else { continue };
                        let p = self.find(a, x).unwrap();
                        return Some(if y_first { format!("({q} {op} {p})") } else { format!("({p} {op} {q})") });
                    }
                }
            }
        }
        if n > SMALL {
            self.dead.insert((s, t));
        }
        None
    }

    fn solve(&mut self, cards: &[i64], goal: i64) -> Option<String> {
        self.cards = cards.to_vec();
        self.cards.sort();
        self.eq = (1..cards.len()).filter(|&i| self.cards[i] == self.cards[i - 1]).map(|i| 1 << i).sum();
        self.sets.clear();
        self.dead.clear();
        let s = self.find((1 << cards.len()) - 1, (goal, 1))?;
        Some(if cards.len() > 1 { s[1..s.len() - 1].to_string() } else { s })
    }
}

fn run<S: AsRef<str>>(solver: &mut Solver, words: &[S]) -> Result<String, String> {
    let nums = words.iter().map(|w| w.as_ref().parse::<i64>().map_err(|e| format!("{}: {e}", w.as_ref())));
    let nums = nums.collect::<Result<Vec<i64>, _>>()?;
    let Some((&goal, cards)) = nums.split_last().filter(|(_, c)| !c.is_empty()) else {
        return Err("usage: solve24 CARD... GOAL".into());
    };
    // Every numerator/denominator formed is at most 2^(k-1) * product(leaves) for an expression
    // with k leaves, and the search only forms expressions over the cards plus the goal.
    // ponytail: plain i64, so that bound (goal included) must fit; i128 would lift the ceiling.
    let bound = cards.iter().try_fold(1i64, |p, &c| p.checked_mul(2)?.checked_mul(c.checked_abs()?.max(1)));
    if bound.is_none() || goal < 0 || cards.iter().any(|&c| c < 0) {
        return Err("cards and goal must be non-negative, and cards small enough for exact i64 arithmetic".into());
    }
    if goal > bound.unwrap() {
        return Ok("No solution".into()); // out of reach, and not safe to do arithmetic with
    }
    if bound.unwrap().checked_mul(2 * goal.max(1)).is_none() {
        return Err("cards and goal too large for exact i64 arithmetic".into());
    }
    Ok(match solver.solve(cards, goal) {
        Some(s) => format!("{s} = {goal}"),
        None => "No solution".into(),
    })
}

fn line(solver: &mut Solver, line: &str) -> String {
    run(solver, &line.split_whitespace().collect::<Vec<_>>()).unwrap_or_else(|e| format!("error: {e}"))
}

fn main() {
    let args: Vec<String> = std::env::args().skip(1).collect();
    let stdin = || std::io::stdin().lock().lines().map(|l| l.unwrap());
    if args.is_empty() {
        let mut solver = Solver::default();
        stdin().for_each(|l| println!("{}", line(&mut solver, &l)));
    } else if args[0] == "-j" {
        // Batch mode: unlike the default it reads all of stdin before answering.
        let threads = args.get(1).and_then(|n| n.parse().ok()).filter(|&n| n > 0 && args.len() == 2);
        let Some(threads) = threads else {
            eprintln!("usage: solve24 -j THREADS < games");
            std::process::exit(2);
        };
        let games: Vec<String> = stdin().collect();
        // ponytail: contiguous chunks, and each thread builds its own value sets, so below a few
        // thousand games more than ~4 threads buys nothing. Sharing the sets (Arc) would fix that.
        let out = std::thread::scope(|sc| {
            let chunks = games.chunks(games.len().div_ceil(threads).max(1));
            let work = |c: &[String]| {
                let mut solver = Solver::default();
                c.iter().map(|l| line(&mut solver, l)).collect::<Vec<_>>()
            };
            let jobs: Vec<_> = chunks.map(|c| sc.spawn(move || work(c))).collect();
            jobs.into_iter().flat_map(|j| j.join().unwrap()).collect::<Vec<_>>()
        });
        print!("{}", out.iter().map(|l| format!("{l}\n")).collect::<String>());
    } else {
        match run(&mut Solver::default(), &args) {
            Ok(s) => println!("{s}"),
            Err(e) => {
                eprintln!("{e}");
                std::process::exit(2);
            }
        }
    }
}

#[cfg(test)]
// Reference: forward search over every ordered pair and operator, negative intermediates included.
fn brute(hand: &[R], goal: i64) -> bool {
    if hand.len() == 1 {
        return hand[0] == (goal, 1);
    }
    (0..hand.len()).any(|i| {
        (0..hand.len()).filter(|&j| j != i).any(|j| {
            let rest = (0..hand.len()).filter(|&k| k != i && k != j).map(|k| hand[k]);
            "+-*/".chars().filter(|&op| op != '/' || hand[j].0 != 0).any(|op| {
                let v = raw(hand[i], hand[j], op);
                brute(&rest.clone().chain([r(v.0 * v.1.signum(), v.1.abs())]).collect::<Vec<_>>(), goal)
            })
        })
    })
}

#[test]
fn self_check() {
    let solve = |cards: &[i64], goal| Solver::default().solve(cards, goal);
    let run = |words: &[&str]| run(&mut Solver::default(), words);
    assert_eq!(r(6, 4), (3, 2));
    assert_eq!(r(0, 5), (0, 1));
    assert_eq!(r(-3, 2), (-3, 2));
    let mut set = Set::new();
    for v in [(6, 4), (3, 2), (0, 7), (5, 1), (1 << 60, 1 << 59), (3 << 55, 5 << 55)] {
        set.insert(v);
    }
    assert_eq!(set.vals, [(6, 4), (0, 7), (5, 1), (1 << 60, 1 << 59), (3 << 55, 5 << 55)]);
    assert!(set.contains((9, 6)) && set.contains((0, 1)) && set.contains((10, 5)) && set.contains((3, 5)));
    assert!(!set.contains((1, 1)) && !set.contains((7, 4)) && !set.contains((5, 3)));
    // the last one is 6 / (1 - 3 / 4): needs small / large
    for (cards, goal) in [(&[4, 7, 8, 8][..], 24), (&[3, 3, 8, 8], 24), (&[1, 5, 5, 5], 24), (&[1, 3, 4, 6], 24)] {
        assert!(solve(cards, goal).is_some(), "{cards:?}");
    }
    assert_eq!(solve(&[2, 5], 3).unwrap(), "5 - 2");
    assert_eq!(solve(&[2, 6], 3).unwrap(), "6 / 2");
    assert!(solve(&[7, 7, 2, 5], 0).is_some()); // zero intermediates are kept
    assert_eq!(solve(&[0, 5], 0).unwrap(), "0 * 5");
    assert!(solve(&[1, 3, 9], 3).is_some());
    assert!(solve(&[3, 4], 0).is_none());
    for cards in [[1, 1, 1, 1], [1, 1, 1, 2], [1, 6, 7, 8]] {
        assert!(solve(&cards, 24).is_none(), "{cards:?}");
    }
    assert!(solve(&[1, 1, 1, 1, 1, 1, 1], 999).is_none());
    assert_eq!(solve(&[7], 7).unwrap(), "7");
    // against the reference, one solver for all games so the kept value sets are exercised too:
    // every 4-card hand from 0..=10 (lookups only), then 5 and 6 cards (the recursing path)
    let mut solver = Solver::default();
    let mut check = |cards: &[i64], goal: i64| {
        let want = brute(&cards.iter().map(|&c| (c, 1)).collect::<Vec<_>>(), goal);
        assert_eq!(solver.solve(cards, goal).is_some(), want, "{cards:?} {goal}");
    };
    for (a, b, c, d) in (0..=10).flat_map(|a| (a..=10).flat_map(move |b| (b..=10).flat_map(move |c| (c..=10).map(move |d| (a, b, c, d))))) {
        check(&[d, b, a, c], 24);
        check(&[a, b, c, d], a * 7 + 1);
    }
    let mut seed = 24u64;
    let mut card = || {
        seed = seed.wrapping_mul(6364136223846793005).wrapping_add(1442695040888963407);
        (seed >> 33) as i64 % 10 + 1
    };
    for i in 0..30 {
        let hand: Vec<i64> = (0..5 + i / 29).map(|_| card()).collect();
        check(&hand, 100 + card() * 37 + i);
    }
    assert_eq!(run(&["3", "8", "24"]).unwrap(), "3 * 8 = 24");
    assert_eq!(run(&["3", "8", "1000000000000"]).unwrap(), "No solution");
    assert!(run(&["24"]).is_err() && run(&["x", "1"]).is_err() && run(&["-3", "8", "24"]).is_err() && run(&["3", "8", "-5"]).is_err());
    assert!(run(&["4000000000", "4000000000", "4000000000", "1"]).is_err());
    assert_eq!(line(&mut Solver::default(), "3 3 8 8 24"), "8 / (3 - (8 / 3)) = 24");
}
