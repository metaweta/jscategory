// By Michael Stay
// (c) 2013-2017

// Library of contracts and functors.
// TODO: cache typing judgements on functions in a WeakMap.
define(() => {
  const call = Function.prototype.call;
  const slice = call.bind([].slice);
  const getClassName = call.bind({}.toString);
  const create = Object.create.bind(Object);

  // A contract that allows anything
  const any = (x) => x;

  // Contracts for special values
  const undef = (x) => {
    if (x !== void 0) { throw new TypeError(`Expected undefined, got ${JSON.stringify(x)}.`); }
    return x;
  };
  const nul = (x) => {
    if (x !== null) { throw new TypeError(`Expected null, got ${JSON.stringify(x)}.`); }
    return x;
  };
  const nan = (x) => {
    if (x === x) { throw new TypeError(`Expected NaN, got ${JSON.stringify(x)}.`); }
    return x;
  };

  // Creates a contract that tests the [[Class]]
  // internal property of the object.
  const classOf = (s) => (v) => {
    const className = getClassName(v);
    if (className !== '[object ' + s + ']') {
      throw new TypeError(`Expected ${s}, got ${className}.`);
    }
    return v;
  };

  const array = classOf('Array');
  const date = classOf('Date');
  const regexp = classOf('RegExp');
  const promise = classOf('Promise');

  const re = r => {
      regexp(r);
      return x => {
          if (!string(x).match(r)) {
              throw new TypeError(`Expected a matching string, got ${x}.`);
          }
          return x;
      };
  };

  const promOf = (c) => (x) => {
    return x.then(c);
  };

  // Creates a contract for a value of type s
  const typeOf = (s) => (v) => {
    const type = typeof v;
    if (type !== s) {
      throw new TypeError(`Expected ${s}, got ${type}.`);
    }
    return v;
  };

  const func = typeOf('function'); 
  const string = typeOf('string');
  const object = typeOf('object');
  const boolean = typeOf('boolean');
  const number = typeOf('number');
  const symbol = typeOf('symbol');

  // Creates a contract for an object inheriting from ctor
  const instanceOf = (ctor) => (inst) => {
    if (!(inst instanceof ctor)) {
      throw new TypeError(`Expected an instance of ${ctor.name}${inst.constructor ? `, got an instance of ${inst.constructor.name}.` : ''}`);
    }
    return inst;
  };

  // Asserts n is a signed 32-bit number
  const int32 = (n) => {
    if ((n | 0) !== n) {
      throw new TypeError(`Expected a 32-bit integer, got ${JSON.stringify(n)}.`);
    }
    return n;
  };

  // Asserts int32 and nonnegative
  const nat32 = (n) => {
    if ((n | 0) !== n || n < 0) {
      throw new TypeError(`Expected a 32-bit natural, got ${JSON.stringify(n)}.`);
    }
    return n;
  };

  const int53 = (n) => {
    if (Math.abs(n) < Math.pow(2, 53) && Number.isInteger(n)) {
      return n;
    }
    throw new TypeError(`Expected an integer n such that Math.abs(n) < Math.pow(2, 53), got ${JSON.stringify(n)}.`);
  };
  
  const nat53 = (n) => {
    if (n >= 0 && n < Math.pow(2, 53) && Number.isInteger(n)) {
      return n;
    }
    throw new TypeError(`Expected a natural n such that n < Math.pow(2, 53), got ${JSON.stringify(n)}.`);
  };
  
  // Creates a contract for an array whose
  // elements all satisfy the contract c
  const arrayOf = (c) => {
    func(c);
    // The function passed to map here
    // restricts c to one argument.
    return (a) => array(a).map(x => c(x));
  };

  // Creates a contract for an object whose
  // enumerable properties all satisfy the contract c
  const objectOf = (c) => {
    func(c);
    return (o) => {
      object(o);
      const result = create(o);
      for (i in o) {
        result[i] = c(o[i]);
      }
      return result;
    };
  };

  // Given an array of contracts, creates a contract for
  // an array whose elements satisfy the respective contracts:
  // the product of the given contracts, indexed by numbers
  const prodn = (cs) => {
    arrayOf(func)(cs);
    const len = cs.length;
    return (args) => {
      array(args);
      if (args.length !== len) {
        throw new TypeError(`Expected ${len} elements, got ${args.length}.`);
      }
      const result = [];
      for (let i = 0; i < len; ++i) {
        // Apply each contract to the
        // corresponding argument.
        result[i] = cs[i](args[i]);
      }
      return result;
    };
  };

  // Given an object whose enumerable properties are contracts,
  // creates a contract for an object whose enumerable properties
  // satisfy the respective contracts: the product of the given
  // contracts, indexed by strings.
  const prods = (cs) => {
    object(cs);
    for (let i in cs) {
      func(cs[i]);
    }
    return (x) => {
      const y = Object.create(object(x));
      for (let i in cs) {
        y[i] = cs[i](x[i]);
      }
      return y;
    };
  };

  // Same as prods but modifies the object directly to preserve
  // object identity.
  const interface = (cs) => {
    object(cs);
    for (let i in cs) {
      func(cs[i]);
    }
    return (x) => {
      for (let i in cs) {
        x[i] = cs[i](x[i]);
      }
      return x;
    };
  };

  // Given an array of contracts, creates a contract for a
  // 2-element array where item 0 is an index and item 1
  // is a value satisfying the contract at that index
  // in the array: the coproduct of the given contracts,
  // tagged by numbers.
  const coprodn = (cs) => {
    arrayOf(func)(cs);
    return (choice) => {
      array(choice);
      nat32(choice[0]);
      if (choice.length !== 2) {
        throw new TypeError(`Expected [nat32, any], got ${choice.length} elements.`);
      }
      if (choice[0] >= cs.length) {
        throw new TypeError(`Tag out of range: expected number in [0, ${cs.length}), got ${choice[0]}.`)
      }
      choice[1] = cs[choice[0]](choice[1]);
      return choice;
    };
  };

  // Given an object of contracts, creates a contract for a
  // 2-element array where item 0 is a property name and item 1
  // is a value satisfying the contract at that property name
  // in the object: the coproduct of the given contracts,
  // tagged by strings.
  const coprods = (cs) => {
    objectOf(func)(cs);
    return (choice) => {
      array(choice);
      string(choice[0]);
      if (choice.length !== 2) {
        throw new TypeError(`Expected [string, any], got ${choice.length} elements.`);
      }
      if (!cs.hasOwnProperty(choice[0])) {
        throw new TypeError(`Unknown tag: ${choice[0]}`)
      }
      choice[1] = cs[choice[0]](choice[1]);
      return choice;
    };
  };

  // Given an array of contracts, apply all of them.
  // This is the product in the category of sets and inclusions.
  const intersect = (cs) => {
    arrayOf(func)(cs);
    const len = cs.length;
    return (x) => {
      let result = x;
      for (let i = 0; i < len; ++i) {
        result = cs[i](result);
      }
      return result;
    };
  };

  // Given an array of contracts, succeed if any succeeds.
  // This is the coproduct in the category of sets and inclusions.
  const union = (cs) => {
    arrayOf(func)(cs);
    const len = cs.length;
    return (x) => {
      for (let i = 0; i < len; ++i) {
        try {
          return cs[i](x);
        } catch (e) { }
      }
      throw new TypeError(`No match among unioned types: got ${JSON.stringify(x)}.`)
    };
  };

  // Given an array of functions, returns a contract
  // for those arrays where the elements all map to the
  // same value under the given functions, e.g. given
  // [f, g], we get a contract for those [x, y] for which
  // f(x) === g(y): the pullback of the functions f and g.
  const pbn = (fs) => {
    const c = prodn(fs);
    const len = fs.length;
    return (args) => {
      array(args);
      const result = c(args);
      for (let i = 1; i < len; ++i) {
        if (result[i] !== result[0]) {
          throw new TypeError(
              `Failed to match pullback constraint in position ${i}: got ${JSON.stringify(result[i])}`);
        }
      }
      return args;
    };
  };

  // TODO: pushouts

  // Helper for the hom functor below.
  // hom(a,b).self(contractForThis)(function method(){...})(args...)
  // Using prods and hom.self to define an interface:
  // const Fooable = prods({
  //   foo: hom(int32, string).self(Fooable);    
  // });
  
  const self = function(c) {
    func(c);
    return (method) => {
      // Here, 'this' is bound to the output of the hom functor,
      // a contract.
      // this(method) checks the pre/post conditions on method
      method = this(method);
      const result = function () {
        // Here, 'this' is the object on which 'method' is being
        // invoked. c(this) checks that it is being invoked
        // on the right kind of object
        return method.apply(c(this), arguments);
      };
      result.toString = () => method.toString();
      return result;
    };
  };

  // Marker for optional arguments:
  // hom(a, opt(b))
  class Optional {
    constructor(c) {
      this.c = c;
    }
  }
  
  const opt = (c) => new Optional(c);

  // Creates a contract for a function whose inputs and output
  // satisfy the given contracts.
  const hom = function(/* input1, ..., inputn, output */) {
    const inputs = slice(arguments, 0, arguments.length - 1);
    let optional = 0, flag = false;
    
    inputs.forEach((input, i) => {
      if (input instanceof Optional) {
        flag = true;
        optional++;
        inputs[i] = input.c;
      } else if (flag) {
        throw new TypeError(
          'Optional arguments must all be at the end.');
      }
    });
    
    arrayOf(func)(inputs);
    
    let precond;
    if (optional === 0) {
      precond = prodn(inputs);
    } else {
      const products = [];
      for (let i = optional; i >= 0; --i) {
        products[i] = prodn(inputs.slice(0, inputs.length - i));
      }
      precond = union(products);
    }
    
    const postcond = func(arguments[arguments.length - 1]);
    const result = (middle) => {
      func(middle);
      const result = function () {
        return postcond(
               middle.apply(this, 
               precond(slice(arguments))));
      };
      result.toString =
          ((str) => () => str + '/* guarded */')('' + middle);
      return result;
    };
    result.self = self.bind(result);
    return result;
  };
    
  // Returns a memoized version of c.
  const memo = (c) => {
    c = hom(any, any)(c);
    const memo = new Map();
    return (key) => {
      if (memo.has(key)) {
        return memo.get(key);
      }
      memo.set(key, c(key));
      return key;
    };
  };
  
  return {
    allOf: intersect,
    any,
    anyOf: union,
    array,
    arrayOf,
    boolean,
    coprodn,
    coprods,
    date,
    func,
    hom,
    id: any,
    instanceOf,
    int32,
    int53,
    intersect,
    interface,
    memo,
    nan,
    nat32,
    nat53,
    nul,
    number,
    object,
    objectOf,
    opt,
    pbn,
    prodn,
    prods,
    promOf,
    promise,
    re,
    regexp,
    string,
    symbol,
    undef,
    union
  };
});
