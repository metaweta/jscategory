// Algebraic theory of MONOIDS:
// Choose a set and two functions satisfying some relations, get a monoid
// It's undecidable to test the relations, so we leave them out...
var monoid = function (set, times, ident) {
  return prods({
    t: func,
    "*": hom(set, set, set),
    1: set
  })({
    t: set,
    "*": times,
    1: ident
  });
};

// ... and write tests instead.
// Given a monoid and a way to get random elements of the monoid,
// check associativity and unit laws.
var testMonoid = function (mon, rand) {
  var a = rand(), b = rand(), c = rand();
  var i = mon[1];
  var t = mon["*"];
  if (t(a, t(b, c)) !== t(t(a, b), c)) {
    throw new Error("Monoid is not associative: " + stringify([a, b, c]));
  }
  if (t(a, i) !== a) {
    throw new Error("Monoid does not satisfy a * 1 = a: " + a);
  }
  if (t(i, a) !== a) {
    throw new Error("Monoid does not satisfy 1 * a = a: " + a);
  }
};

// Alternate definition of a monoid that helps illustrate
// the concept of a monoid homomorphism
var monoid2 = function (setIn, setOut, times, ident) {
  // Allow the other signature as well
  if (arguments.length === 3) {
    ident = times;
    times = setOut;
    setOut = setIn;
  }
  return prods({
    "*": hom(setIn, setIn, setOut),
    1: hom(/*terminal,*/ setOut)
  })({
    "*": times,
    1: ident
  });
};

var K = function (x) { return function () { return x; }; };

var and = hom(boolean, boolean, boolean)(function (b1, b2) { return b1 && b2; });
var andMon = monoid2(boolean, and, K(true));

var xor = hom(boolean, boolean, boolean)(function (b1, b2) { return (b1 ^ b2) ? true : false; });
var xorMon = monoid2(boolean, xor, K(true));

var int32Add = hom(int32, int32, int32)(function (n1, n2) { return n1 + n2; });
var int32AddMon = monoid2(int32, int32Add, K(0));

var concat = hom(string, string, string)(function (s1, s2) { return s1 + s2; });
var concat = monoid2(string, concat, K(""));

var mod2 = hom(int32, boolean)(function (n) { return (n % 2) ? true : false; });
var lsb1 = monoid2(mod2, boolean, xor, K(true));
var lsb2 = monoid2(int32, mod2, int32Add, K(0));
// TODO: monoid hom as pullback of the two ways of computing lsb

// MONADS as monoid objects in an endofunctor category
var monad = function (ftor, times, ident) {    // var monoid = function (set, times, ident) {
  return function (t) {
    func(t);                                   
    return prods({                             //   return prods({
      t: func,                                 //     t: func,
      "*": hom(ftor(ftor(t)), ftor(t)),        //     "*": hom(set, set, set),
      1: hom(t, ftor(t))                       //     1: hom(set)
    })({                                       //   })({
      t: ftor(t),                              //     t: set,
      "*": times(t),                           //     "*": times,
      1: ident(t)                              //     1: ident
    });                                        //   });
  };                                           // };
}

var lift = function (t) {
  func(t);
  return hom(t, arrayOf(t))(function (x) { return [x]; });
};
var flatten = function (t) {
  func(t);
  return hom(arrayOf(arrayOf(t)), arrayOf(t))(function (llx) {
    var result = [];
    var len = llx.length;
    for (var i = 0; i < len; ++i) {
      result = result.concat(llx[i]);
    }
    return result;
  });
};

var listMon = monad(arrayOf, flatten, lift);
var loi = listMon(int32);
try {
  loi.t([3,6,5]); // passes
  loi.t(["3",6,5]); // fails on item 0
} catch (e) {}
loi[1](3); // === [3]
loi["*"]([[1,2],[3,4],[5]]); // === [1,2,3,4,5]

var upto = hom(int32, arrayOf(int32))(function (x) {
  var r = [];
  for (var i = 0; i < x; ++i) {
    r.push(i);
  }
  return r;
});

loi["*"](listMon(upto).t([6,2])); // === [0,1,2,3,4,5,0,1]

// MONADS in the Haskell / Kleisli style
var kleisli = function (mon) {
  return function (t) {
    var mont = mon(t);
    function M(mx) {
      return {
        value: mx,
        _: function (f) {
          return M(mont["*"](mon(f).t(this.value)));
        }
      };
    }
    return function (x) { return M(mont[1](x)); };
  };
};

var kli = kleisli(listMon)(int32);
kli(6)._(upto)._(upto).value; // === [0,0,1,0,1,2,0,1,2,3,0,1,2,3,4]

// Example of a monoidal closed functor, the "points" functor
// Comes equipped with natural isomorphisms
//    chi:(lazy A -o B) -> (lazy A -o lazy B)
//    phi:(lazy prod_i A_i) -> (prod_i lazy A_i)
// http://www.cse.chalmers.se/~rjmh/Papers/whyfp.pdf 
// has lots of examples showing how laziness helps modularization

var lazy = function (c) {
  // Restrict hom to a single argument,
  // i.e. [] -> c
  return hom(c);
};

var lazyLift = K;

var lazyFlatten = function (lazyLazyX) {
  return lazyLazyX();
};

var lazyMon = monad(lazy, lazyLift, lazyFlatten);

var lazyChi = function (lazyAtoB) {
  return function (lazyA) {
    return lazyLift(lazyAtoB()(lazyA()));
  };
};

var lazyPhi = function (lazyProd) {
  // Invoke the lazy prod to get the actual prod,
  // then delay each element.
  return array(lazyProd()).mapClean(lazyLift);
};

// Another monoidal closed functor, 
//    continuation passing is double negation.
// Dinatural in Z:
//    cp A = (A->Z)->Z
var cp = function (c) {
  return hom(hom(c, id), id);
};

var cpLift = function (x) {
  return function (k) {
    return k(x);
  };
};

// Quadruple negation to double negation
// (((X->Z)->Z)->Z)->Z -> (X->Z)->Z
var cpFlatten = function (cpCpX /*: (((X->Z)->Z)->Z)->Z */) {
  return function (k /*: (X->Z) */) {
    return cpCpX(function (l) {
      return l(k); /*: Z */
    });
  };
};

var cpMon = monad(cp, cpLift, cpFlatten);

var cpChi = function (k /*: ((A->B)->Z)->Z */) {
  return function (l /*: (A->Z)->Z */) {
    return function (m /*: B->Z */) {
      return l(function (c /*: A */) {
        return k(function (d /*: A->B */) {
          return m(d(c));
        });
      });
    };
  };
};

// ((prod_i A_i)->Z)->Z -> prod_i (((A_i)->Z)->Z)
var cpPhi = function (cpProd) {
  var prod;
  cpProd(function (p) { prod = array(p); });
  return p.mapClean(cpLift);
};
