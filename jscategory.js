// Library of contracts and functors.
// TODO: cache typing judgements on functions in a WeakMap.
define(() => {
  let call = Function.prototype.call;
  let slice = call.bind([].slice);
  let getClassName = call.bind({}.toString);
  let create = Object.create.bind(Object);

  // A contract that allows anything
  let any = (x) => x;

  // Contracts for special values
  let undef = (x) => {
    if (x !== void 0) { throw new TypeError('Expected undefined.'); }
    return x;
  };
  let nul = (x) => {
    if (x !== null) { throw new TypeError('Expected null.'); }
    return x;
  };
  let nan = (x) => {
    if (x === x) { throw new TypeError('Expected NaN.'); }
    return x;
  };

  // Creates a contract that tests the [[Class]]
  // internal property of the object.
  let classOf = (s) => (v) => {
    if (getClassName(v) !== '[object ' + s + ']') {
      throw new TypeError('Expected ' + s);
    }
    return v;
  };

  let array = classOf('Array');
  let date = classOf('Date');
  let regexp = classOf('RegExp');
  let re = r => {
      regexp(r);
      return x => {
          if (!string(x).match(r)) {
              throw new TypeError('Expected a matching string.');
          }
          return x;
      };
  };

  // Creates a contract for a value of type s
  let typeOf = (s) => (v) => {
    if (typeof v !== s) {
      throw new TypeError('Expected a' + 
          (s === 'object' ? 'n ' : ' ') + s + '.');
    }
    return v;
  };

  let func = typeOf('function'); 
  let string = typeOf('string');
  let object = typeOf('object');
  let boolean = typeOf('boolean');
  let number = typeOf('number');

  // Creates a contract for an object inheriting from ctor
  let instanceOf = (ctor) => (inst) => {
    if (!(inst instanceof ctor)) {
      throw new TypeError('Expected an instance of ' + ctor);
    }
    return inst;
  };

  // Asserts n is a signed 32-bit number
  let int32 = (n) => {
    if ((n | 0) !== n) {
      throw new TypeError('Expected a 32-bit integer.');
    }
    return n;
  };

  // Asserts int32 and nonnegative
  let nat32 = (n) => {
    if ((n | 0) !== n || n < 0) {
      throw new TypeError('Expected a 32-bit natural.');
    }
    return n;
  };

  // Creates a contract for an array whose
  // elements all satisfy the contract c
  let arrayOf = (c) => {
    func(c);
    // The function passed to map here
    // restricts c to one argument.
    return (a) => array(a).map(x => c(x));
  };

  // Creates a contract for an object whose
  // enumerable properties all satisfy the contract c
  let objectOf = (c) => {
    func(c);
    return (o) => {
      object(o);
      let result = create(o);
      for (i in o) {
        result[i] = c(o[i]);
      }
      return result;
    };
  };

  // Given an array of contracts, creates a contract for
  // an array whose elements satisfy the respective contracts:
  // the product of the given contracts, indexed by numbers
  let prodn = (cs) => {
    arrayOf(func)(cs);
    let len = cs.length;
    return (args) => {
      array(args);
      if (args.length !== len) {
        throw new TypeError('Expected ' + len + ' elements');
      }
      for (let i = 0; i < len; ++i) {
        // Apply each contract to the
        // corresponding argument.
        args[i] = cs[i](args[i]);
      }
      return args;
    };
  };

  // Given an object whose enumerable properties are contracts,
  // creates a contract for an object whose enumerable properties
  // satisfy the respective contracts: the product of the given
  // contracts, indexed by strings.
  let prods = (cs) => {
    object(cs);
    for (let i in cs) {
      func(cs[i]);
    }
    return (x) => {
      object(x);
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
  let coprodn = (cs) => {
    arrayOf(func)(cs);
    return (choice) => {
      array(choice);
      nat32(choice[0]);
      if (choice.length !== 2) {
        throw new TypeError('Expected [nat32, any].');
      }
      if (choice[0] >= cs.length) {
        throw new TypeError('Tag out of range.')
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
  let coprods = (cs) => {
    objectOf(func)(cs);
    return (choice) => {
      array(choice);
      string(choice[0]);
      if (choice.length !== 2) {
        throw new TypeError('Expected [string, any].');
      }
      if (!cs.hasOwnProperty(choice[0])) {
        throw new TypeError('Unknown tag.')
      }
      choice[1] = cs[choice[0]](choice[1]);
      return choice;
    };
  };

  // Given an array of contracts, apply all of them.
  // This is the product in the category of sets and inclusions.
  let intersect = (cs) => {
    arrayOf(func)(cs);
    let len = cs.length;
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
  let union = (cs) => {
    arrayOf(func)(cs);
    let len = cs.length;
    return (x) => {
      for (let i = 0; i < len; ++i) {
        try {
          return cs[i](x);
        } catch (e) { }
      }
      throw new TypeError('No match among unioned types.')
    };
  };

  // Given an array of functions, returns a contract
  // for those arrays where the elements all map to the
  // same value under the given functions, e.g. given
  // [f, g], we get a contract for those [x, y] for which
  // f(x) === g(y): the pullback of the functions f and g.
  let pbn = (fs) => {
    let c = prodn(fs);
    let len = fs.length;
    return (args) => {
      array(args);
      let result = c(args);
      for (let i = 1; i < len; ++i) {
        if (result[i] !== result[0]) {
          throw new TypeError(
              'Failed to match pullback constraint in position ' + i);
        }
      }
      return args;
    };
  };

  // TODO: pushouts

  // Helper for the hom functor below.
  // hom(a,b).self(contractForThis)(function method(){...})(args...)
  let self = (c) => {
    func(c);
    let homab = this;
    return (method) => {
      // homab(method) checks the pre/post conditions on method
      method = homab(method);
      let result = function (letArgs) {
        // c(this) checks that it is being invoked
        // on the right kind of object
        return method.apply(c(this), arguments);
      };
      result.toString = () => method.toString();
      return result;
    };
  };

  // Creates a contract for a function whose inputs and output
  // satisfy the given contracts.
  let hom = function(/* input1, ..., inputn, output */) {
    let precond = prodn(arrayOf(func)(
        slice(arguments, 0, arguments.length - 1)));
    let postcond = func(arguments[arguments.length - 1]);
    let result = (middle) => {
      func(middle);
      let result = function (letArgs) {
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
  
  // Using prods and hom.self to define an interface:
  // let Fooable = prods({
  //   foo: hom(int32, string).self(Fooable);    
  // });
  
  
  // Returns a memoized version of c.
  let memo = (c) => {
    c = hom(any, any)(c);
    let memo = new Map();
    return (key) => {
      if (memo.has(key)) {
        return memo.get(key);
      }
      memo.set(key, c(key));
      return key;
    };
  };
  
  let promOf = (c) => (x) => {
    return x.then(c);
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
    intersect,
    memo,
    nan,
    nat32,
    nul,
    number,
    object,
    objectOf,
    pbn,
    prodn,
    prods,
    promOf,
    re,
    regexp,
    string,
    undef,
    union
  };
});
