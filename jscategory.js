// Library of contracts and functors.
// TODO: cache typing judgements on functions in a WeakMap.
define(() => {
  var call = Function.prototype.call;
  var slice = call.bind([].slice);
  var getClassName = call.bind({}.toString);
  var create = Object.create.bind(Object);

  // A contract that allows anything
  var any = (x) => x;

  // Contracts for special values
  var undef = (x) => {
    if (x !== void 0) { throw new TypeError('Expected undefined.'); }
    return x;
  };
  var nul = (x) => {
    if (x !== null) { throw new TypeError('Expected null.'); }
    return x;
  };
  var nan = (x) => {
    if (x === x) { throw new TypeError('Expected NaN.'); }
    return x;
  };

  // Creates a contract that tests the [[Class]]
  // internal property of the object.
  var classOf = (s) => (v) => {
    if (getClassName(v) !== '[object ' + s + ']') {
      throw new TypeError('Expected ' + s);
    }
    return v;
  };

  var array = classOf('Array');
  var date = classOf('Date');
  var regexp = classOf('RegExp');

  // Creates a contract for a value of type s
  var typeOf = (s) => (v) => {
    if (typeof v !== s) {
      throw new TypeError('Expected a' + 
          (s === 'object' ? 'n ' : ' ') + s + '.');
    }
    return v;
  };

  var func = typeOf('function'); 
  var string = typeOf('string');
  var object = typeOf('object');
  var boolean = typeOf('boolean');
  var number = typeOf('number');

  // Creates a contract for an object inheriting from ctor
  var instanceOf = (ctor) => (inst) => {
    if (!(inst instanceof ctor)) {
      throw new TypeError('Expected an instance of ' + ctor);
    }
    return inst;
  };

  // Asserts n is a signed 32-bit number
  var int32 = (n) => {
    if ((n | 0) !== n) {
      throw new TypeError('Expected a 32-bit integer.');
    }
    return n;
  };

  // Asserts int32 and nonnegative
  var nat32 = (n) => {
    if ((n | 0) !== n || n < 0) {
      throw new TypeError('Expected a 32-bit natural.');
    }
    return n;
  };

  // Creates a contract for an array whose
  // elements all satisfy the contract c
  var arrayOf = (c) => {
    func(c);
    // The function passed to map here
    // restricts c to one argument.
    return (a) => array(a).map(x => c(x));
  };

  // Creates a contract for an object whose
  // enumerable properties all satisfy the contract c
  var objectOf = (c) => {
    func(c);
    return (o) => {
      object(o);
      var result = create(o);
      for (i in o) {
        result[i] = c(o[i]);
      }
      return result;
    };
  };

  // Given an array of contracts, creates a contract for
  // an array whose elements satisfy the respective contracts:
  // the product of the given contracts, indexed by numbers
  var prodn = (cs) => {
    arrayOf(func)(cs);
    var len = cs.length;
    return (args) => {
      array(args);
      if (args.length !== len) {
        throw new TypeError('Expected ' + len + ' arguments');
      }
      var result = [];
      for (var i = 0; i < len; ++i) {
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
  var prods = (cs) => {
    object(cs);
    for (var i in cs) {
      func(cs[i]);
    }
    return (x) => {
      object(x);
      var result = create(x);
      for (var i in cs) {
        result[i] = cs[i](x[i]);
      }
      return result;
    };
  };

  // Given an array of contracts, creates a contract for a
  // 2-element array where item 0 is an index and item 1
  // is a value satisfying the contract at that index
  // in the array: the coproduct of the given contracts,
  // tagged by numbers.
  var coprodn = (cs) => {
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
      return [choice[0], cs[choice[0]](choice[1])];
    };
  };

  // Given an object of contracts, creates a contract for a
  // 2-element array where item 0 is a property name and item 1
  // is a value satisfying the contract at that property name
  // in the object: the coproduct of the given contracts,
  // tagged by strings.
  var coprods = (cs) => {
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
      return [choice[0], cs[choice[0]](choice[1])];
    };
  };

  // Given an array of contracts, apply all of them.
  // This is the product in the category of sets and inclusions.
  var intersect = (cs) => {
    arrayOf(func)(cs);
    var len = cs.length;
    return (x) => {
      var result = x;
      for (var i = 0; i < len; ++i) {
        result = cs[i](result);
      }
      return result;
    };
  };

  // Given an array of contracts, succeed if any succeeds.
  // This is the coproduct in the category of sets and inclusions.
  var union = (cs) => {
    arrayOf(func)(cs);
    var len = cs.length;
    return (x) => {
      for (var i = 0; i < len; ++i) {
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
  var pbn = (fs) => {
    var c = prodn(fs);
    var len = fs.length;
    return (args) => {
      array(args);
      var result = c(args);
      for (var i = 1; i < len; ++i) {
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
  var self = (c) => {
    func(c);
    var homab = this;
    return (method) => {
      // homab(method) checks the pre/post conditions on method
      method = homab(method);
      var result = function (varArgs) {
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
  var hom = (/* input1, ..., inputn, output */) => {
    var precond = prodn(arrayOf(func)(
        slice(arguments, 0, arguments.length - 1)));
    var postcond = func(arguments[arguments.length - 1]);
    var result = (middle) => {
      func(middle);
      var result = function (varArgs) {
        return postcond(
               middle.apply(this, 
               precond(slice(arguments))));
      };
      result.toString =
          ((str) => () => str + '/* guarded */';)('' + middle);
      return result;
    };
    result.self = self.bind(result);
    return result;
  };
  
  // Using prods and hom.self to define an interface:
  // var Fooable = prods({
  //   foo: hom(int32, string).self(Fooable);    
  // });
  
  
  // Returns a memoized version of c.
  var memo = (c) => {
    c = hom(any, any)(c);
    var memo = new WeakMap();
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
    any: any,
    anyOf: union,
    array: array,
    arrayOf: arrayOf,
    boolean: boolean,
    coprodn: coprodn,
    coprods: coprods,
    date: date,
    func: func,
    hom: hom,
    id: any,
    instanceOf: instanceOf,
    int32: int32,
    intersect: intersect,
    memo: memo,
    nan: nan,
    nat32: nat32,
    nul: nul,
    number: number,
    object: object,
    objectOf: objectOf,
    pbn: pbn,
    prodn: prodn,
    prods: prods,
    regexp: regexp,
    string: string,
    undef: undef,
    union: union,
  };
});
