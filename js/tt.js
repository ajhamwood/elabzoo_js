var TT = (options = {}) => {
  let { debug, which } = options, count = 0,
      debugFn = p => ({}, prop) => p ? console[prop] : () => {};
debug = (p => new Proxy({}, { get (...args) { return debugFn(p)(...args) } }))(debug);

  class Result {  // Error handling
    constructor (fn) {
      let chain = () => count++ < 100000 ? this : new Proxy({}, { get(){ return () => {} } });
      let thrown = false, value = null, error = v => (thrown = true, v),
          join = (fn, v = value) => (r => { Result.prototype.isPrototypeOf(r) &&
            (x => value = "ok" in x ? x.ok : error(x.err))(r.unwrap()); debug.log(value); })
            (value = fn(v, error));
      this.then = fn => chain(thrown || join(fn));  // On resolve
      this.catch = fn => chain(thrown && (thrown = false, join(fn)));  // On reject
      this.unwrap = () => ({ [ thrown ? "err" : "ok" ]: value });  // Await
      this.toPromise = () => new Promise((ok, err) => this.then(s => ok(s)).catch(e => err(e)));
      return fn(v => join(() => v), e => join(() => error(e)))
    }
    static pure (v) { return new Result(r => r(v)) }  // Resolve
    static throw (e) { return new Result(({}, l) => l(e)) }  // Reject
  }

  class AST {
    static tag = class AST {};
    constructor (nodes, wc) {
      for (let node in nodes) {
        this[node] = (([props, meths = {}]) => ({ [node]: class extends AST.tag {
          constructor (...args) { super();
            for (let i = 0; i < args.length && i < props.length; i++) this[props[i]] = args[i];
            for (let meth in meths) meths[meth] = Object.assign((f => ({ [meth]: function () {
              return f.apply(this, arguments)
            } })[meth])(meths[meth]), { withContext: wc(meths[meth], () => this) });
            Object.assign(this, meths)
          } get [Symbol.toStringTag] () { return node }
        } })[node])(nodes[node])
      }
    }
  }

  class Parser {
    static seq (ps) { return state => ps.reduce((acc, p) => acc.then(p), Result.pure(state)) }
    static do (ps) { return state => ps.reduceRight((acc, p) => (...ss) => p(...ss).then(s => acc(...ss, s)))(state) }
    static reql (p1, p2) { return state => p1(state).then(s1 => p2({ ...s1, data: state.data })) }
    static reqr (p1, p2) { return state => p1(state).then(s1 => p2(s1).then(s2 => ({ ...s2, data: s1.data }))) }
    static map (p, fn) { return state => p(state).then(s => ({ ...s, data: fn(s.data) })) }
    static mapFull (p, fn) { return state => p(state).then(fn) }
    // static subst (p, data) { return state => p(state).then(s2 => ({ ...s2, data })) }

    // static fail (state) { return new Result((ok, err) => err({ ...state, fail: "_"})) }
    // static err (msg) { return state => new Result.throw({ ...state, fail: msg }) }
    // static lookahead (p) { return state => p(state).then(() => state) }
    static cut (p, msg) { return state => p(state)  // include error merging fn?
      .catch((e, err) => err({ ...e, fail: `${e.fail}\n${msg}` })) }
    static peek (p) { return state => p(state)
      .catch((e, err) => err({ ...state, fail: e.fail[0] === "_" ? e.fail : "_" + e.fail })) }
    static alt (p1, p2) { return state => p1(state)
      .catch((e, err) => e.fail[0] === "_" ? p2(state) : err(e)) }
    static choice (ps) { return state => ps
      .reduce((acc, p) => Parser.alt(acc, p))(state) }
    static option (p) { return state => Parser.alt(p, Result.pure)(state) }

    static any ({ source, offset, pos: [row, col], data }) { return new Result((ok, err) => source.length <= offset ?
      err({ source, offset, pos: [row, col], data, fail: "_Any char" }) :
      ok({ source, pos: /\r\n?|\n/g.test(source[offset]) ?
        [row + 1, 1] : [row, col + 1], data: source[offset], offset: offset + 1 })) }
    static eof ({ source, offset, pos, data }) { return new Result((ok, err) => source.length > offset ?
      err({ source, offset, pos, data, fail: "_EOF" }) :
      ok({ source, offset, pos, data: "" })) }
    static satisfy (pred, msg) { return Parser.peek(state => Parser.any(state)
      .then((s, err) => pred(s) ? s : err({ ...s, fail: msg ?? "_Satisfy" }))) }
    static char (c) { return Parser.satisfy(s => s.data === c, `_Char ${c}`) }
    static many (p) { return Parser.cut(state => ((loop = (s, res) => p(s)
      .then(st => loop(st, res.concat([st.data])))
      .catch(({ fail, ...st }, err) => res.length ?
        ({ ...st, data: res }) : err({ ...st, fail }))) => loop(state, []))(), "Many") }
    static scan (pred, msg) { return state => Parser.many(s1 => Parser.any(s1).then((s2, err) => 
      s2.source.length <= s2.offset ? err({ ...state, fail: msg ?? "_Scan" }) :
        !pred(s2) ? s2 : err({ ...s2, fail: "_" })))(state)  // Use symbol?
      .catch((s3, err) => s3.fail === "_" ? err(s3) : s3) }
    static guard (p, pred, msg) { return state => p(state)
      .then((s, err) => pred(s.data) ? s : err({ ...state, fail: msg ?? "_Guard" })) }
    
    constructor (cmb, ast, wc) {
      for (let k in cmb)
        cmb[k] = Object.assign((f => ({ [k]: function () {
          debug.group(k);
          let res = f.apply({ ...cmb, ...ast }, arguments);
          debug.groupEnd();
          return res
        } })[k])(cmb[k]), { withContext: wc(cmb[k], () => ({ ...cmb, ...ast })) });
      this.parse = source => Result.pure({ source, offset: 0, pos: [1, 0], data: null })
        .then(cmb.parse)
        .catch((e, err) => err({ message: e.fail[0] === "_" ? "Unmanaged parser error: " + e.fail.slice(1) : e.fail }))
    }
  }

  class Evaluator {  // TODO: first match?
    static match (sw, ...argNames) {
      let tree = {}, branch;
      for (let k in sw) {
        let cls = k.split(" "), prev, i;
        branch = tree;
        for (i = 0; i < cls.length; i++) {
          if (!(cls[i] in branch)) branch[cls[i]] = {};
          [ prev, branch ] = [ branch, branch[cls[i]] ]
        }
        prev[cls[i - 1]] = (f => ({ [k]: function () {
          debug.log(k, ...arguments);
          return f.apply(this, arguments) } })[k])(sw[k])
      }
      return function (obj = {}) {
        let branch = tree, _;
        for (let argName of argNames) {
          let name = obj[argName].constructor.name.toLowerCase();
          if (name in branch) {
            if ("_" in branch) ({ _ } = branch);
            branch = branch[name]
          } else if ("_" in branch) return branch._.apply(this, [obj]);
          else if (typeof _ !== "undefined") return _.apply(this, [obj]);
          else Result.throw({ message: "No matching clauses" })
        }
        return branch.apply(this, [obj])
      }
    }
    constructor (fns, ast, wc, ctx, exps) {
      for (let k in fns)
        fns[k] = Object.assign((f => ({ [k]: function () {
          let { source, phase, ...c } = ctx;
          debug.group(k, "|", ...Object.entries(arguments[0]).flatMap(([k, v], i, ar) => [`${k}:`,
            AST.tag.isPrototypeOf(v.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]), "| arg:", arguments[0], ", ctx:", c);
          let res = f.apply({ ...fns, ...ast }, arguments);
          debug.groupEnd();
          return res
        } })[k])(fns[k]), { withContext: wc(fns[k], () => ({ ...fns, ...ast })) });
      for (let emeth of exps) this[emeth] = fns[emeth]
    }
  }

  class Context {
    constructor ({contextData = {}, astData, parserData, evaluatorData: [ edata, ...eexports ], debugHandler}) {
      let optCtx = (o, ctx) => o.constructor.name === "Function" ? o(ctx) : o,
          withContext = (fn, clf) => (newCtx, args, cb = x => x) => {
            let keepCtx = { ...contextData, env: [...contextData.env], types: [...contextData.types] };
            Object.assign(contextData, newCtx);
            let res = cb(fn.apply(clf(), args));
            Object.assign(contextData, keepCtx);
            return res },
          ast = new AST(optCtx(astData, contextData), withContext),
          parser = new Parser(optCtx(parserData, contextData), ast, withContext),
          evaluator = new Evaluator(optCtx(edata, contextData), ast, withContext, contextData, eexports),
          phase = true;
      Object.defineProperty(this, "phase", { get () { return phase } });
      this.parse = (...args) => { phase = "parser"; debugFn = debugHandler; return parser.parse(...args) };
      for (let emeth of eexports) this[emeth] = (...args) => { phase = "evaluator"; debugFn = debugHandler; return evaluator[emeth](...args) }
    }
  }

  // Untyped lambda calculus
  let ulc = new Context({
        debugHandler: p => ({}, prop) => p !== true && p !== ulc.phase ? () => {} : console[prop],

        astData: {
          RVar: [ [ "ix" ], { toString () { return `${this.ix}` } } ],
          RApp: [ [ "func", "arg" ], { toString (prec = false) { return (str => prec ? `(${str})` : str)
            (this.func.constructor.name === "RApp" ?
              `${this.func.func.toString(false)} ${this.func.arg.toString(true)} ${this.arg.toString(true)}` :
              `${this.func.toString(true)} ${this.arg.toString(true)}`) } } ],
          RLam: [ [ "body" ], { toString (prec = false) { return (str => prec ? `(${str})` : str)
            (`\\ ${this.body.toString(false)}`) } } ],
          RLet: [ [ "term", "next" ], { toString () {
            return `let ${this.term.toString(false)};\n${this.next.toString(false)}` } } ],
          VVar: [ [ "lvl" ] ],
          VApp: [ [ "func", "arg" ] ],
          VLam: [ [ "env" ] ]
        },

        parserData: {
          ws (state) { return Parser.many(Parser.choice([
            Parser.satisfy(s => /[^\S\r\n]/g.test(s.data), "_HWS"),
            Parser.satisfy(s => /\r\n?|\n/g.test(s.data), "_VWS"),
            Parser.seq([ this.symbol("--"), Parser.scan(s => /\r\n?|\n/g.test(s.data), "_Comment") ])
          ]))(state) },
          parens (p) { return state => Parser.reql(
            Parser.seq([ Parser.char("("), Parser.option(this.ws) ]),
            Parser.reqr(p, Parser.seq([ Parser.char(")"), Parser.option(this.ws) ])))(state) },
          symbol (str) { return state => Parser.map(Parser.guard(
            Parser.many(Parser.satisfy(s => s.data === str[s.offset - state.offset - 1], "Keyword: " + str)),
            data => data.length === str.length), data => data.join(""))(state) },
          keyword (str) { return Parser.reqr(this.symbol(str), Parser.option(this.ws)) },
          keyword_ (str) { return Parser.reqr(this.symbol(str), this.ws) },
          
  
          ix (state) { return Parser.many(Parser.satisfy(s => /\d/g.test(s.data), "_Index"))(state) },
          atom (state) { return Parser.reqr(Parser.alt(
            Parser.map(this.ix, data => new this.RVar(parseInt(data))),
            this.parens(this.term)), Parser.option(this.ws))(state) },
          spine (state) { return Parser.map(Parser.many(this.atom),
            data => data.reduce((acc, atom) => new this.RApp(acc, atom)))(state) },
  
          lam (state) { return Parser.seq([ this.keyword("\\"),
            Parser.map(this.term, data => new this.RLam(data)) ])(state) },
          let (state) { return Parser.seq([ this.keyword_("let"), this.term,
            Parser.do([ Parser.seq([ this.keyword(";"), this.term ]),
              (t, u) => ({ ...u, data: new this.RLet(t.data, u.data) }) ]) ])(state) },
  
          term (state) { return Parser.choice([ this.lam, this.let, this.spine ])(state) },
          parse (state) {
            debug.log("Parse:");
            return Parser.seq([ Parser.option(this.ws), Parser.reqr(this.term, Parser.eof) ])(state) }
        },

        evaluatorData: [ {
          eval: Evaluator.match({
            rvar ({ term, env }) { return env[env.length - term.ix - 1] },
            rapp ({ term, env }) { return ((func, arg) => func.constructor.name === "VLam" ?
              this.cApp(func.env, arg) : new this.VApp(func, arg))
              (this.eval({ env, term: term.func }), this.eval({ env, term: term.arg })) },
            rlam ({ term, env }) { return new this.VLam({ term: term.body, env }) },
            rlet ({ term, env }) { return this.eval({ term: term.next,
            env: env.concat([this.eval({ env, term: term.term })]) }) }
          }, "term"),
          cApp ({ term, env }, val) { return this.eval({ term, env: env.concat([val]) }) },
          quote: Evaluator.match({
            vvar ({ lvl, val }) { return new this.RVar(lvl - val.lvl - 1) },
            vapp ({ lvl, val }) { return new this.RApp(this.quote({ lvl, val: val.func }), this.quote({ lvl, val: val.arg })) },
            vlam ({ lvl, val }) { return new this.RLam(this.quote({ lvl: lvl + 1, val: this.cApp(val.env, new this.VVar(lvl)) })) }
          }, "val"),
  
          nf ({ data: term, env = [] }) {
            debug.log("Normal form:");
            return { term: this.quote({ lvl: env.length, val: this.eval({ term, env }) }) }
          }
        }, "nf" ]
      })

  // Dependent types
  let dt = new Context({
        debugHandler: p => ({}, prop) => p !== true && p !== dt.phase ? () => {} :
          prop === "log" ? (v, ...rest) => {
            let declutter = v => { if (v.hasOwnProperty("source")) { let { source, ...o } = v; return [o] } else return [v] };
            console.log(...(typeof v === "string" ? [v] : declutter(v)), ...rest.flatMap(declutter)
              .flatMap((o, i) => [ ...(i === 0 ? ["|"] : []), "{", ...Object.entries(o).flatMap(([k, v], i, ar) => [`${k}:`, typeof v === "string" ? `\`${v}\`` :
                AST.tag.isPrototypeOf(v.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]), "}"])) } : console[prop],
        
        contextData: { env: [], types: [], lvl: 0, source: null },

        astData: ctx => ({
          RVar: [ [ "name", "pos" ], { toString () { return `RVar ${this.name}` } } ],
          RLam: [ [ "name", "body", "pos" ], { toString () { return `RLam ${this.name}. ${this.body}` } } ],
          RApp: [ [ "func", "arg", "pos" ], { toString () { return `(${this.func} :@: ${this.arg})` } } ],
          RU: [ [ "pos" ], { toString () { return "RU" } } ],
          RPi: [ [ "name", "dom", "cod", "pos" ], { toString () {
            return `RPi (${this.name} : ${this.dom}) -> ${this.cod}` } } ],
          RLet: [ [ "name", "type", "term", "next", "pos" ],
            { toString () { return `let ${this.name} : ${this.type} = ${this.term};\n${this.next}` } } ],
  
          Var: [ [ "ix" ], { toString () { return ctx.types[ctx.types.length - this.ix - 1]?.[0] ?? `?{${ctx.types.length - this.ix - 1}}` } } ],
          App: [ [ "func", "arg" ], { toString (prec = 0) { return (str => prec > 2 ? `(${str})` : str)
            (`${this.func.toString(2)} ${this.arg.toString(3)}`) } } ],
          Lam: [ [ "name", "body" ], {
            fresh (name) { return name === "_" ? "_" : ctx.types.reduce((acc, [n]) => new RegExp(`^${acc}[']*$`).test(n) ? n + "'" : acc, name) },
            toString (prec = 0) {
              let name = this.fresh(this.name),
                  goLam = (name, body) => {
                    let keepCtx = { ...ctx, env: [...ctx.env], types: [...ctx.types] };
                    if (name) ctx.types.push([name]);
                    let res = (name => body.constructor.name !== "Lam" ? `. ${body.toString(0)}` :
                          ` ${name}${goLam(name, body.body)}`)(this.fresh(body.name));
                    Object.assign(ctx, keepCtx);
                    return res
                  };
              return (str => prec > 0 ? `(${str})` : str)(`λ ${name}${goLam(name, this.body)}`) } } ],
          Pi: [ [ "name", "dom", "cod" ], {
            fresh (name) { return name === "_" ? "_" : ctx.types.reduce((acc, [n]) => new RegExp(`^${acc}[']*$`).test(n) ? n + "'" : acc, name) },
            toString (prec = 0) {
              let name = this.fresh(this.name),
                  piBind = (name, dom) => (`(${name} : ${dom.toString(0)})`),
                  goPi = (name, cod) => {
                    let keepCtx = { ...ctx, env: [...ctx.env], types: [...ctx.types] };
                    if (name) ctx.types.push([name]);
                    let res = cod.constructor.name !== "Pi" ? ` → ${cod.cod.toString(1)}` :
                          cod.name !== "_" ? (name => piBind(name, cod.dom) + goPi(name, cod.cod))(this.fresh(name)) :
                            ` → ${cod.dom.toString(2)} → ${cod.cod.toString.withContext({ types: ctx.types.concat([["_"]])}, [1]) }`;
                    Object.assign(ctx, keepCtx);
                    return res
                  };
              return (str => prec > 1 ? `(${str})` : str)
                (name === "_" ? `${this.dom.toString(2)} → ${this.cod.toString.withContext({ types: ctx.types.concat([["_"]]) }, [1])}` :
                piBind(name, this.dom) + goPi(name, this.cod)) } } ],
          U: [ [], { toString () { return "U" } } ],
          Let: [ [ "name", "type", "term", "next" ], {
            fresh (name) { return name === "_" ? "_" : ctx.types.reduce((acc, [n]) => new RegExp(`^${acc}[']*$`).test(n) ? n + "'" : acc, name) },
            toString (prec = 0) { let name = this.fresh(this.name); return (str => prec > 0 ? `(${str})` : str)
              (`let ${name} : ${this.type.toString(0)}\n    = ${this.term.toString(0)};\n${this.next.toString
                .withContext({ types: ctx.types.concat([[name]]) }, [0])}`) } } ],
  
          VVar: [ [ "lvl" ] ],
          VApp: [ [ "func", "arg" ] ],
          VLam: [ [ "name", "cls" ] ],
          VPi: [ [ "name", "dom", "cls" ] ],
          VU: [[]]
        }),

        parserData: ctx => ({
          inc: (i => () => i++)(0),

          ws (state) { return Parser.many(Parser.choice([
            Parser.satisfy(s => /[^\S\r\n]/g.test(s.data), "_HWS"),
            Parser.satisfy(s => /\r\n?|\n/g.test(s.data), "_VWS"),
            Parser.seq([ this.symbol("--"), Parser.scan(s => /\r\n?|\n/g.test(s.data), "_Comment") ])
          ]))(state) },
          parens (p) { return Parser.reql(
            Parser.seq([ Parser.char("("), Parser.option(this.ws) ]),
            Parser.reqr(p, Parser.seq([ Parser.char(")"), Parser.option(this.ws) ]))) },
          symbol (str) { return state => Parser.map(Parser.guard(
            Parser.many(Parser.satisfy(s => s.data === str[s.offset - state.offset - 1], "Symbol: " + str)),
            data => data.length === str.length), data => data.join(""))(state) },
          keyword (str) { return Parser.reqr(this.symbol(str), Parser.option(this.ws)) },
          keyword_ (str) { return Parser.reqr(this.symbol(str), this.ws) },
          ident (state) { return Parser.reqr(Parser.seq([
            Parser.satisfy(s => /[a-zA-Z_]/.test(s.data)),
            Parser.do([ Parser.alt(Parser.many(Parser.satisfy(s => /[a-zA-Z_0-9]/.test(s.data))), s => ({ ...s, data: [] })),
              (s, t) => ({ ...t, data: s.data + t.data.join("") })]) ]), Parser.option(this.ws))(state) },

          atom (state) { return Parser.choice([
            Parser.mapFull(Parser.guard(this.ident, data => !~["let", "U", "_"].findIndex(x => x === data)),
              s => ({ ...s, data: new this.RVar(s.data, s.pos) })),
            Parser.mapFull(this.keyword("U"), s => ({ ...s, data: new this.RU(s.pos) })),
            this.parens(this.term) ])(state) },

          binder (state) { return Parser.alt(this.ident, this.keyword("_"))(state) },
          spine (state) { return Parser.map(Parser.many(this.atom),
            data => data.reduce((acc, atom) => new this.RApp(acc, atom)))(state) },

          lam (state) { return Parser.seq([ this.keyword("\\"), Parser.many(this.binder),
            Parser.do([ Parser.seq([ this.keyword("."), this.term ]),
              (t, u) => ({ ...u, data: t.data.reduceRight((acc, b) =>
                new this.RLam(b, acc, u.pos), u.data) }) ]) ])(state) },

          namedPi (state) { return Parser.seq([
            Parser.many(this.parens(Parser.seq([
              Parser.many(Parser.mapFull(this.binder, s => ({ ...s, data: [s.data, s.pos] }))),
              Parser.do([ Parser.seq([ this.keyword(":"), this.term ]),
                (s, t) => ({ ...t, data: s.data.map(([b, pos]) => [b, t.data, pos]) }) ]) ]))),
            Parser.do([ Parser.seq([ this.keyword("->"), this.term ]),
              (s, t) => ({ ...t, data: s.data.flat(1).reduce((acc, [b, tm, pos]) =>
                new this.RPi(b, tm, acc, pos, this.inc()), t.data) }) ]) ])(state) },
          anonPiOrSpine (state) { return Parser.seq([ this.spine,
            Parser.option(Parser.do([ Parser.reql(this.keyword("->"), this.term),
              (s, t) => ({ ...t, data: new this.RPi("_", s.data, t.data, t.pos, this.inc()) }) ])) ])(state) },

          let (state) { return Parser.seq([ this.keyword_("let"), this.binder,
            Parser.do([ Parser.seq([ this.keyword(":"), this.term ]),
              ({}, s) => Parser.seq([ this.keyword("="), this.term ])(s),
              ({}, {}, s) => Parser.seq([ this.keyword(";"), this.term ])(s),
              (s, t, u, v) => ({ ...v, data: new this.RLet(s.data, t.data, u.data, v.data, v.pos) }) ]) ])(state) },
            
          term (state) { return Parser.choice([ this.lam, this.let, this.namedPi, this.anonPiOrSpine ])(state) },
          parse (state) {
            ctx.source = state.source;
            debug.log("Parse:");
            return Parser.seq([ Parser.option(this.ws), Parser.reqr(this.term, Parser.eof) ])(state) }
        }),

        evaluatorData: [ ctx => ({
          eval: Evaluator.match({
            var ({ term, env }) { return env[env.length - term.ix - 1] },
            app ({ term, env }) { return ((func, arg) => func.constructor.name === "VLam" ?
              this.cApp({ cls: func.cls, val: arg }) : new this.VApp(func, arg))
              (this.eval({ env, term: term.func }), this.eval({ env, term: term.arg })) },
            lam ({ term, env }) { return new this.VLam(term.name, { term: term.body, env }) },
            pi ({ term, env }) { return new this.VPi(term.name, this.eval({ term: term.dom, env }), { term: term.cod, env }) },
            u () { return new this.VU() },
            let ({ term, env }) { return this.eval({ term: term.next, env: env.concat([this.eval({ env, term: term.term })]) }) }
          }, "term"),
          cApp ({ cls: { term, env }, val }) { return this.eval({ term, env: env.concat([val]) }) },
          quote: Evaluator.match({
            vvar ({ lvl, val }) { return new this.Var(lvl - val.lvl - 1) },
            vapp ({ lvl, val }) { return new this.App(this.quote({ lvl, val: val.func }), this.quote({ lvl, val: val.arg })) },
            vlam ({ lvl, val }) { return new this.Lam(val.name, this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VVar(lvl) }) })) },
            vpi ({ lvl, val }) { return new this.Pi(val.name, this.quote({ lvl, val: val.dom }),
              this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VVar(lvl) }) })) },
            vu () { return new this.U() }
          }, "val"),

          conv: Evaluator.match({
            "vu vu" () { return true },
            "vpi vpi" ({ lvl, val0, val1 }) { return this.conv({ lvl, val0: val0.dom, val1: val1.dom }) && this.conv({ lvl: lvl + 1,
              val0: this.cApp({ cls: val0.cls, val: new this.VVar(lvl) }),
              val1: this.cApp({ cls: val1.cls, val: new this.VVar(lvl) }) }) },
            "vlam vlam" ({ lvl, val0, val1 }) { return this.conv({ lvl: lvl + 1,
              val0: this.cApp({ cls: val0.cls, val: new this.VVar(lvl) }),
              val1: this.cApp({ cls: val1.cls, val: new this.VVar(lvl) }) }) },
            "vlam _" ({ lvl, val0, val1 }) { return this.conv({ lvl: lvl + 1,
              val0: this.cApp({ cls: val0.cls, val: new this.VVar(lvl) }),
              val1: new this.VApp(val1, new this.VVar(lvl)) }) },
            "vvar vvar" ({ val0, val1 }) { return val0.lvl === val1.lvl },
            "vapp vapp" ({ lvl, val0, val1 }) { return this.conv({ lvl, val0: val0.func, val1: val1.func }) &&
              this.conv({ lvl, val0: val0.arg, val1: val1.arg }) },
            _ ({ lvl, val0, val1 }) { return val1.constructor.name === "VLam" && this.conv({ lvl: lvl + 1,
              val0: new this.VApp(val0, new this.VVar(lvl)),
              val1: this.cApp({ cls: val1.cls, val: new this.VVar(lvl) }) }) }
          }, "val0", "val1"),
          define ({ name, val, vtype }) { return {
            env: ctx.env.concat([ val ]),
            types: ctx.types.concat([[ name, vtype ]]),
            lvl: ctx.lvl + 1, source: ctx.source
          } },

          check: Evaluator.match({
            "rlam vpi" ({ term, vtype }) { return this.check.withContext(this.define({ name: term.name, val: new this.VVar(ctx.lvl), vtype: vtype.dom }),
              [ { term: term.body, vtype: this.cApp({ cls: vtype.cls, val: new this.VVar(ctx.lvl) }) } ], res => res
                .then(body => new this.Lam(term.name, body))) },
            "rlet _" ({ term, vtype }) { return this.check({ term: term.type, vtype: new this.VU() })
              .then(type => {
                let cvtype = this.eval({ term: type, env: ctx.env }), { name } = term;
                return this.check({ term: term.term, vtype: cvtype })
                  .then(term => this.check.withContext(define({ name: term.name, val: this.eval({ term, env: ctx.env }), vtype: cvtype }),
                    [ { term: term.next, vtype } ], res => res
                      .then(nx => this.Let(name, type, term, nx)))) }) },
            _ ({ term, vtype }) { return this.infer({ term })
              .then(({ term: t, vtype: vt }) => this.conv({ lvl: ctx.lvl, val0: vt, val1: vtype }) ? t :
                Result.throw({ pos: term.pos, msg: `Type mismatch\n    Expected type:\n    ${this.quote({ val: vtype, lvl: ctx.lvl })
                  }\n    Inferred type:\n    ${this.quote({ val: vt, lvl: ctx.lvl })}` })) }
          }, "term", "vtype"),
          infer: Evaluator.match({
            rvar ({ term }) { let ix = ctx.types.findIndex(([x]) => x === term.name);
              return ~ix ? Result.pure({ term: new this.Var(ctx.lvl - ix - 1), vtype: ctx.types[ix][1] }) :
                Result.throw({ pos: term.pos, msg: "Variable out of scope: " + term.name }) },
            rapp ({ term }) { return this.infer({ term: term.func })
              .then(({ term: func, vtype }) => vtype.constructor.name === "VPi" ?
                this.check({ term: term.arg, vtype: vtype.dom }).then(arg => ({
                  term: new this.App(func, arg),
                  vtype: this.cApp({ cls: vtype.cls, val: this.eval({ term: arg, env: ctx.env }) }) })) :
                Result.throw({ pos: term.func.pos,
                  msg: `Expected a function type, instead inferred:\n    ${this.quote({ val: vtype, lvl: ctx.lvl })}` })) },
            rlam ({ term }) { return Result.throw({ pos: term.pos, msg: "Can't infer type for lambda expression" }) },
            rpi ({ term }) { return this.check({ term: term.dom, vtype: new this.VU() })
              .then(dom => this.check.withContext(
                this.define({ name: term.name, val: new this.VVar(ctx.lvl), vtype: this.eval({ term: dom, env: ctx.env }) }),
                [ { term: term.cod, vtype: new this.VU() } ], res => res
                  .then(cod => ({ term: new this.Pi(term.name, dom, cod), vtype: new this.VU() })))) },
            ru () { return Result.pure({ term: new this.U(), vtype: new this.VU() }) },
            rlet ({ term }) { return this.check({ term: term.type, vtype: new this.VU() })
              .then(type => {
                let cvtype = this.eval({ term: type, env: ctx.env }), { name } = term;
                return this.check({ term: term.term, vtype: cvtype })
                  .then(termexpr => this.infer.withContext(this.define({ name: term.name, val: this.eval({ term: termexpr, env: ctx.env }), vtype: cvtype }),
                    [ { term: term.next } ], res => res.then(({ term: next, vtype }) => ({ term: new this.Let(name, type, termexpr, next), vtype })))) }) }
          }, "term"),

          type ({ data: term, env = [] }) {
            debug.log("Typecheck term:");
            return this.infer({ term, env })
              .then(({ vtype }) => ({ type: this.quote({ lvl: 0, val: vtype }) }))
              .catch(this.displayError) },
          nf ({ data: term, env = [] }) {
            debug.log("Normal form:");
            return this.infer({ term, env })
              .then(({ term, vtype }) => ({
                term: this.quote({ lvl: 0, val: this.eval({ term, env: [] }) }),
                type: this.quote({ lvl: 0, val: vtype }) }))
              .catch(this.displayError) },
          displayError ({ msg, pos }, err) {
            let lines = ctx.source.split(/\r\n?|\n/);
            return err({ message: `${lines[pos[0] - 1]}\n${"-".repeat(pos[1] - 1) + "^ " + pos}\n${msg}` })
          }
        }), "nf", "type" ]
      });

  const sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  return Object.defineProperties({}, {
    import: { get() {
      return opt => sequence(() => new Promise((ok, err) => {
        opt ??= {};
        if ("code" in opt && !("path" in opt)) ok(opt.code);
        else if ("path" in opt) fetch(opt.path).then(rsp => rsp.text()).then(ok);
        else err({ message: "Load error: option object malformed or missing" });
      }).then(src => ({ ready: ({
        1: { nf: { run: () => ulc.parse(src).then(ulc.nf).toPromise() } },
        2: {
          nf: { run: () => dt.parse(src).then(dt.nf).toPromise() },
          type: { run: () => dt.parse(src).then(dt.type).toPromise() }
        }
      })[which ?? 1] })))
    } },
    select: { get() { return i => which = i } }
  })
}