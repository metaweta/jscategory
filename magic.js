// Turn Array into a monad.
// Usual definition of flatten; see, e.g.
// http://goo.gl/lLQpes
Object.defineProperty(Array.prototype, "flatten", {
  enumerable:false, 
  writable:true, 
  configurable:true, 
  value: function () {
    return this.reduce(function (previous, current) {
      return previous.concat(current);
    });
  }
});

// L-system for growing trees; see, e.g. 
// https://www.khanacademy.org/computer-programming/tree/1029209629
// twig: Array<number>
function makeGrow(twig) {
  // number => Array<number>
  return function grow(n) {
    if (n === 0) { return twig; }
    if (n === 1) { return [1, 1]; }
    return [n];
  };
}

// Abstract Maybe class 
function Maybe() { throw Error("abstract!"); }
Maybe.prototype.map = function (f) {
  if (this instanceof Some) {
    return some(f(this.v));
  } else {
    return none;
  }
};
Maybe.prototype.flatten = function () {
  if (this instanceof Some) {
    return this.v;
  } else {
    return none;
  }
};
// Concrete constructors for Maybe
function Some(v) { this.v = v; }
Some.prototype = Object.create(Maybe.prototype);
Some.prototype.toString = function () { return "some(" + JSON.stringify(this.v) + ")"; };
function some(v) { return new Some(v); }
function None() { }
None.prototype = Object.create(Maybe.prototype);
None.prototype.toString = function () { return "none"; };
var none = new None();

// invert:number => Maybe<number>
function invert(n) {
  if (n === 0) { return none; }
  return some(1/n);
}

// Magical stuff here
var M = (function () {
  // Computation stack in case we have nested monadic
  // bind expressions
  var stack = [];
  
  // Magic 1: when an object is used as an argument to
  // greater-than, its valueOf function is invoked. The
  // default implementation for function objects isn't
  // side-effecting, but we can make it map the function
  // over the state and then flatten (i.e. monadic bind
  // is map followed by the monadic multiplication).
  // This implementation is independent of the map and
  // flatten methods of the object on the top of the stack.
  Function.prototype.valueOf = function () {
    if (stack[0] && stack[0].map) {
      stack[0] = stack[0].map(this).flatten();
    }
    return this;
  };
  
  // Magic 2: the result of an expression involving
  // greater-than is a boolean.  We can add a property to
  // booleans that pops the result off the stack.
  Object.defineProperty(Boolean.prototype, "_", {
    get: function() {
      return stack.pop();
    }
  });

  
  
  // Monadic unit pushes state onto the top of the stack.
  return {
    array: function (s) { stack.push([s]); },
    maybe: function (s) { stack.push(some(s)); }
  };
})();

// Choose a nice twig.
var grow = makeGrow([1,4,2,0,5,1,4,3,0,5,0]);
// Grow it twice.
console.log( (M.array(0) > grow > grow)._ );

// Inverting twice is the identity on non-zero numbers
console.log('' + (M.maybe(5) > invert > invert)._ );
// Inverting twice is undefined on zero
console.log('' + (M.maybe(0) > invert > invert)._ );
