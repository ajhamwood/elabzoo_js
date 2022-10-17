var TT = (options = {}) => {
  let { debug, which } = options, count = 0,
      debugFn = p => ({}, prop) => p ? console[prop] : () => {};
debug = (p => new Proxy({}, { get (...args) { return debugFn(p)(...args) } }))(debug);

  class Result {  // Error handling
    constructor (fn) {
      let chain = () => /*count++ > 5e3 ? new Proxy({}, { get(){ return () => {} } }) :*/ this;
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
            } })[meth])(meths[meth]), { withContext: wc(() => meths[meth], () => this) });
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
    
    static cut (p, msg) { return state => p(state)  // include error merging fn?
      .catch((e, err) => err({ ...state, fail: e.fail[0] === "_" ? msg : e.fail + (typeof msg === "undefined" ? "" : `\n${msg}`) })) }
    static peek (p) { return state => p(state)
      .catch((e, err) => err({ ...state, fail: "fail" in state && state.fail[0] !== "_" ? state.fail : e.fail[0] === "_" ? e.fail : "_" + e.fail })) }
    static alt (p1, p2) { return state => p1(state)
      .catch((e, err) => e.fail[0] === "_" ? p2(state) : err({ ...state, fail: e.fail })) }
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
    static char (c) { return Parser.satisfy(s => s.data === c, `_Char "${c}"`) }
    static many (p) { return state => ((loop = (s, res) => p(s)
      .then(st => loop(st, res.concat([st.data])))
      .catch(({ fail }, err) => res.length && fail[0] === "_" ?
        ({ ...s, data: res }) : err({ ...s, fail }))) => loop(state, []))() }
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
        } })[k])(cmb[k]), { withContext: wc(() => cmb[k], () => ({ ...cmb, ...ast })) });
      this.parse = source => Result.pure({ source, offset: 0, pos: [1, 0], data: null })
        .then(cmb.parse)
        .catch((e, err) => err({ message: e.fail[0] === "_" ? "Unmanaged parser error" : e.fail }))
    }
  }

  class Evaluator {  // TODO: first match?
    static match (sw, { decorate = () => {}, scrut }) {
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
        let branch = tree, _, match;
        decorate(obj);
        for (let argName of scrut) {
          if (typeof argName !== "string") {
            let [[ procArgName, fn ]] = Object.entries(argName);
            obj[procArgName] = match = fn.apply(this, [obj]);
          } else match = obj[argName];
          let name = match.constructor.name.toLowerCase();
          if (name in branch) {
            if ("_" in branch) ({ _ } = branch);
            branch = branch[name]
          } else if ("_" in branch) return branch._.apply(this, [obj]);
          else if (typeof _ !== "undefined") return _.apply(this, [obj]);
          else return Result.throw({ msg: "Internal error: No matching clauses" })
        }
        return branch.apply(this, [obj])
      }
    }
    constructor (fns, ast, wc, ctx, exps) {
      for (let k in fns)
        fns[k] = Object.assign((f => ({ [k]: function () {
          let { local: { source, phase, ...local } = {}, global = {} } = ctx;
          debug.group(k, "|", ...Object.entries(arguments[0] ?? {}).flatMap(([k, v], i, ar) => [`${k}:`,
            AST.tag.isPrototypeOf(v?.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]),
              "| arg:", arguments[0], ", locals:", local, ", globals:", global);
          let res = f.apply({ ...fns, ...ast }, arguments);
          debug.groupEnd();
          return res
        } })[k])(fns[k]), { withContext: wc(() => fns[k], () => ({ ...fns, ...ast })) });
      for (let emeth of exps) this[emeth] = fns[emeth]
    }
  }

  class Context {
    constructor ({contextData = {}, astData, parserData, evaluatorData: [ edata, ...eexports ], debugHandler}) {
      contextData = { local: contextData.local ?? {}, global: contextData.global ?? {} };
      let optCtx = (o, ctx) => o.constructor.name === "Function" ? o(ctx) : o,
          keepCtx = (o = {}) => Object.fromEntries(Object.entries(o).map(([k, v]) => ([k, v instanceof Array ? [...v] :
            [Map, Set, WeakMap, WeakSet].some(kl => kl === v.constructor) ? new v.constructor([...v.entries()]) : v]))),
          withContext = (fnf, clf) => (newLocalCtx, args, cb = x => x) => {
            let keepLocalCtx = keepCtx(contextData.local);
            Object.assign(contextData.local, newLocalCtx);
            let res = cb(fnf().apply(clf(), args));
            Object.assign(contextData.local, keepLocalCtx);
            return res },
          keepGlobalCtx = keepCtx(contextData.global),
          ast = new AST(optCtx(astData, contextData), withContext),
          parser = new Parser(optCtx(parserData, contextData), ast, withContext),
          evaluator = new Evaluator(optCtx(edata, contextData), ast, withContext, contextData, eexports),
          phase = true;
      Object.defineProperty(this, "phase", { get () { return phase } });
      this.parse = (...args) => {
        phase = "parser";
        debugFn = debugHandler;
        return parser.parse(...args) };
      for (let emeth of eexports) this[emeth] = (...args) => {
        phase = "evaluator";
        debugFn = debugHandler;
        let res = evaluator[emeth](...args);
        Object.assign(contextData.global, keepCtx(keepGlobalCtx));
        return res;
      }
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
          }, { scrut: [ "term" ] }),
          cApp ({ term, env }, val) { return this.eval({ term, env: env.concat([val]) }) },
          quote: Evaluator.match({
            vvar ({ lvl, val }) { return new this.RVar(lvl - val.lvl - 1) },
            vapp ({ lvl, val }) { return new this.RApp(this.quote({ lvl, val: val.func }), this.quote({ lvl, val: val.arg })) },
            vlam ({ lvl, val }) { return new this.RLam(this.quote({ lvl: lvl + 1, val: this.cApp(val.env, new this.VVar(lvl)) })) }
          }, { scrut: [ "val" ] }),
  
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
            let declutter = v => { if (v?.hasOwnProperty("source")) { let { source, ...o } = v; return [o] } else return [v] };
            console.log(...(typeof v === "string" ? [v] : declutter(v)), ...rest.flatMap(declutter)
              .flatMap((o, i) => [ ...(i === 0 ? ["|"] : []), "{", ...Object.entries(o).flatMap(([k, v], i, ar) => [`${k}:`, typeof v === "string" ? `\`${v}\`` :
                AST.tag.isPrototypeOf(v?.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]), "}"])) } : console[prop],
        
        contextData: { local: { env: [], types: [], names: [], lvl: 0, source: null } },

        astData: ({ local: ctx }) => ({
          RVar: [ [ "name", "pos" ], { toString () { return `RVar ${this.name}` } } ],
          RLam: [ [ "name", "body", "pos" ], { toString () { return `RLam ${this.name}. ${this.body}` } } ],
          RApp: [ [ "func", "arg", "pos" ], { toString () { return `(${this.func} :@: ${this.arg})` } } ],
          RU: [ [ "pos" ], { toString () { return "RU" } } ],
          RPi: [ [ "name", "dom", "cod", "pos" ], { toString () {
            return `RPi (${this.name} : ${this.dom}) -> ${this.cod}` } } ],
          RLet: [ [ "name", "type", "term", "next", "pos" ],
            { toString () { return `let ${this.name} : ${this.type} = ${this.term};\n${this.next}` } } ],
  
          Var: [ [ "ix" ], { toString () { let lvl = ctx.types.length - this.ix - 1;
            return lvl >= 0 ? ctx.types[lvl][0] : ctx.names[-1 - lvl] } } ],
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

        parserData: ({ local: ctx }) => ({
          ws (state) { return Parser.many(Parser.choice([
            Parser.satisfy(s => /[^\S\r\n]/g.test(s.data), "_HWS"),
            Parser.satisfy(s => /\r\n?|\n/g.test(s.data), "_VWS"),
            Parser.seq([ this.symbol("--"), Parser.scan(s => /\r\n?|\n/g.test(s.data), "_Comment") ])
          ]))(state) },
          satisfy (pred, msg) { return Parser.seq([ s1 => Parser.peek(Parser.any)(s1).then((s2, err) => /[a-zA-Z_0-9\(\):=;\\.\->\ \r\n]/.test(s2.data) ? s1 :
            err({ ...s1, fail: `Found illegal character "${s2.data}"` })), Parser.satisfy(pred, msg) ]) },
          parens (p) { return Parser.reql(
            Parser.seq([ Parser.char("("), Parser.option(this.ws) ]),
            Parser.reqr(p, Parser.seq([ Parser.cut(Parser.char(")"), "Unclosed parens"), Parser.option(this.ws) ]))) },
          symbol (str) { return state => Parser.map(Parser.guard(
            Parser.many(this.satisfy(s => s.data === str[s.offset - state.offset - 1], `Symbol: "${str}"`)),
            data => data.length === str.length), data => data.join(""))(state) },
          keyword (str) { return Parser.reqr(this.symbol(str), Parser.option(this.ws)) },
          keyword_ (str) { return Parser.reqr(this.symbol(str), this.ws) },
          ident (state) { return Parser.reqr(Parser.seq([
            this.satisfy(s => /[a-zA-Z_]/.test(s.data)),
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
            Parser.do([ Parser.seq([ Parser.cut(this.keyword("."), "Lambda without body"), this.term ]),
              (t, u) => ({ ...u, data: t.data.reduceRight((acc, b) =>
                new this.RLam(b, acc, u.pos), u.data) }) ]) ])(state) },

          namedPi (state) { return Parser.seq([
            Parser.many(this.parens(Parser.seq([
              Parser.many(Parser.mapFull(this.binder, s => ({ ...s, data: [s.data, s.pos] }))),
              Parser.do([ Parser.seq([ this.keyword(":"), this.term ]),
                (s, t) => ({ ...t, data: s.data.map(([b, pos]) => [b, t.data, pos]) }) ]) ]))),
            Parser.do([ Parser.seq([ this.keyword("->"), this.term ]),
              (s, t) => ({ ...t, data: s.data.flat(1).reduceRight((acc, [b, tm, pos]) =>
                new this.RPi(b, tm, acc, pos), t.data) }) ]) ])(state) },
          anonPiOrSpine (state) { return Parser.seq([ this.spine,
            Parser.option(Parser.do([ Parser.reql(this.keyword("->"), this.term),
              (s, t) => ({ ...t, data: new this.RPi("_", s.data, t.data, t.pos) }) ])) ])(state) },

          let (state) { return Parser.seq([ this.keyword_("let"), Parser.cut(this.binder, "Malformed binder"),
            Parser.do([ Parser.seq([ Parser.cut(this.keyword(":"), 'Let missing ":"'), this.term ]),
              ({}, s) => Parser.seq([ Parser.cut(this.keyword("="), 'Let missing "="'), this.term ])(s),
              ({}, {}, s) => Parser.seq([ Parser.cut(this.keyword(";"), 'Let missing ";"'),
                Parser.cut(this.term, "Definition list must end with term expression") ])(s),
              (s, t, u, v) => ({ ...v, data: new this.RLet(s.data, t.data, u.data, v.data, v.pos) }) ]) ])(state) },
            
          term (state) { return Parser.choice([ this.lam, this.let, this.namedPi, this.anonPiOrSpine ])(state) },
          parse (state) {
            ctx.source = state.source;
            debug.log("Parse:");
            return Parser.seq([ Parser.option(this.ws), Parser.reqr(this.term, Parser.eof) ])(state) }
        }),

        evaluatorData: [ ({ local: ctx }) => ({
          eval: Evaluator.match({
            var ({ term, env }) { return env[env.length - term.ix - 1] },
            app ({ term, env }) { return ((func, arg) => func.constructor.name === "VLam" ?
              this.cApp({ cls: func.cls, val: arg }) : new this.VApp(func, arg))
              (this.eval({ env, term: term.func }), this.eval({ env, term: term.arg })) },
            lam ({ term, env }) { return new this.VLam(term.name, { term: term.body, env }) },
            pi ({ term, env }) { return new this.VPi(term.name, this.eval({ term: term.dom, env }), { term: term.cod, env }) },
            u () { return new this.VU() },
            let ({ term, env }) { return this.eval({ term: term.next, env: env.concat([this.eval({ env, term: term.term })]) }) }
          }, { scrut: [ "term" ] }),
          cApp ({ cls: { term, env }, val }) { return this.eval({ term, env: env.concat([val]) }) },
          quote: Evaluator.match({
            vvar ({ lvl, val }) { return new this.Var(lvl - val.lvl - 1) },
            vapp ({ lvl, val }) { return new this.App(this.quote({ lvl, val: val.func }), this.quote({ lvl, val: val.arg })) },
            vlam ({ lvl, val }) { return new this.Lam(val.name, this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VVar(lvl) }) })) },
            vpi ({ lvl, val }) { return new this.Pi(val.name, this.quote({ lvl, val: val.dom }),
              this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VVar(lvl) }) })) },
            vu () { return new this.U() }
          }, { scrut: [ "val" ] }),

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
          }, { scrut: [ "val0", "val1" ] }),

          define ({ name, val, vtype }) { return {
            env: ctx.env.concat([ val ]),
            types: ctx.types.concat([[ name, vtype ]]), names: [name].concat(ctx.names),
            lvl: ctx.lvl + 1, source: ctx.source } },
          check: Evaluator.match({
            "rlam vpi" ({ term, vtype }) { return this.check.withContext(this.define({ name: term.name, val: new this.VVar(ctx.lvl), vtype: vtype.dom }),
              [ { term: term.body, vtype: this.cApp.withContext({ names: [term.name].concat(ctx.names) }, [ { cls: vtype.cls, val: new this.VVar(ctx.lvl) } ]) } ], res => res
                .then(body => new this.Lam(term.name, body))) },
            "rlet _" ({ term, vtype }) { return this.check({ term: term.type, vtype: new this.VU() })
              .then(type => {
                let cvtype = this.eval({ term: type, env: ctx.env }), { name } = term;
                return this.check({ term: term.term, vtype: cvtype })
                  .then(term => this.check.withContext(define({ name: term.name, val: this.eval({ term, env: ctx.env }), vtype: cvtype }),
                    [ { term: term.next, vtype } ], res => res
                      .then(next => this.Let(name, type, term, next)))) }) },
            _ ({ term, vtype }) { return this.infer({ term })
              .then(({ term: t, vtype: vt }) => this.conv({ lvl: ctx.lvl, val0: vt, val1: vtype }) ? t :
                Result.throw({ pos: term.pos, msg: `Type mismatch\n    Expected type:\n    ${this.quote({ val: vtype, lvl: ctx.lvl })
                  }\n    Inferred type:\n    ${this.quote({ val: vt, lvl: ctx.lvl })}` })) }
          }, { scrut: [ "term", "vtype" ] }),
          infer: Evaluator.match({
            rvar ({ term }) { return (ix => ~ix ? Result.pure({ term: new this.Var(ctx.lvl - ix - 1), vtype: ctx.types[ix][1] }) :
              Result.throw({ pos: term.pos, msg: "Variable out of scope: " + term.name }))(ctx.types.findLastIndex(([n]) => n === term.name)) },
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
          }, { scrut: [ "term" ] }),

          nf ({ data: term, env = [] }) {
            debug.log("Normal form:");
            return this.infer({ term, env })
              .then(({ term, vtype }) => ({
                term: this.quote({ lvl: 0, val: this.eval({ term, env: [] }) }),
                type: this.quote({ lvl: 0, val: vtype }) }))
              .catch(this.displayError) },
          type ({ data: term, env = [] }) {
            debug.log("Typecheck term:");
            return this.infer({ term, env })
              .then(({ vtype }) => ({ type: this.quote({ lvl: 0, val: vtype }) }))
              .catch(this.displayError) },
          displayError ({ msg, pos }, err) {
            let lines = ctx.source.split(/\r\n?|\n/);
            return typeof pos === "undefined" ? err({ message: msg }) :
              err({ message: `${lines[pos[0] - 1]}\n${"-".repeat(pos[1] - 1) + "^ " + pos}\n${msg}` }) }
        }), "nf", "type" ]
      });

  let dth = new Context({
        debugHandler: p => ({}, prop) => p !== true && p !== dth.phase ? () => {} :
          prop === "log" ? (v, ...rest) => {
            let declutter = v => { if (v?.hasOwnProperty("source")) { let { source, ...o } = v; return [o] } else return [v] };
            console.log(...(typeof v === "string" ? [v] : declutter(v)), ...rest.flatMap(declutter)
              .flatMap((o, i) => [ ...(i === 0 ? ["|"] : []), "{",
                ...Object.entries(o).flatMap(([k, v], i, ar) => [`${k}:`,
                  typeof v === "string" ? `\`${v}\`` : AST.tag.isPrototypeOf(v?.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]), "}"]),
              (stack => { try { throw new Error('') } catch (e) { stack = e.stack || "" }
                return stack.split(`\n`)[5].replace(/@.*(js)/g, "") })()) } : console[prop],
        
        contextData: {
          local: { env: [], types: [], bds: [], lvl: 0, pos: 0, names: [] },
          global: { metas: new Map(), pos: [], source: "" } },

        astData: ({ local: ctx }) => ({
          RVar: [ [ "name", "pos" ], { toString () { return `RVar ${this.name}` } } ],
          RLam: [ [ "name", "body", "pos" ], { toString () { return `RLam ${this.name}. ${this.body}` } } ],
          RApp: [ [ "func", "arg", "pos" ], { toString () { return `(${this.func} :@: ${this.arg})` } } ],
          RU: [ [ "pos" ], { toString () { return "RU" } } ],
          RPi: [ [ "name", "dom", "cod", "pos" ], { toString () {
            return `RPi (${this.name} : ${this.dom}) -> ${this.cod}` } } ],
          RLet: [ [ "name", "type", "term", "next", "pos" ],
            { toString () { return `let ${this.name} : ${this.type} = ${this.term};\n${this.next}` } } ],
          RHole: [ [ "pos" ], { toString () { return `{?}` } } ],
  
          Var: [ [ "ix" ], { toString () { let lvl = ctx.types.length - this.ix - 1;
            return lvl >= 0 ? ctx.types[lvl][0] : ctx.names[-1 - lvl] } } ],
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
            toString (prec = 0) {  // TODO convert
              let name = this.fresh(this.name),
                  piBind = (name, dom) => (`(${name} : ${dom.toString(0)})`),
                  goPi = (name, cod) => {
                    let keepCtx = { ...ctx, env: [...ctx.env], types: [...ctx.types] };
                    if (name) ctx.types.push([name]);
                    let res = cod.constructor.name !== "Pi" ? ` → ${cod.toString(1)}` :
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
          Meta: [ [ "mvar" ], { toString () { return `?${this.mvar}` } } ],
          InsMeta: [ [ "mvar", "bds" ], { toString (prec) { return (str => prec > 2 ? `(${str})` : str)
            (`?${this.mvar}${ctx.types.filter(({}, i) => this.bds[i]).map(([n]) => ` ${n}`).join("")}`) } } ],  // Defined : 0, Bound : 1
  
          VFlex: [ [ "mvar", "spine" ] ],  // Meta
          VRigid: [ [ "lvl", "spine" ] ],  // Var
          VLam: [ [ "name", "cls" ] ],
          VPi: [ [ "name", "dom", "cls" ] ],
          VU: [[]]
        }),

        parserData: ({ local: ctx, global: gctx }) => ({
          setPos ({ start = gctx.pos[0], end = gctx.pos[1], writable = true }) {
            gctx.pos = [ [ ...start ], [ ...end ] ];
            writable || Object.defineProperty(gctx, "pos", { writable });
            return [ ...gctx.pos ] },
          ws (state) { return Parser.many(Parser.choice([
            Parser.satisfy(s => /[^\S\r\n]/g.test(s.data), "_HWS"),
            Parser.satisfy(s => /\r\n?|\n/g.test(s.data), "_VWS"),
            Parser.seq([ this.symbol("--", false), Parser.scan(s => /\r\n?|\n/g.test(s.data), "_Comment") ])
          ]))(state) },
          satisfy (pred, msg) { return state => "fail" in state && state.fail[0] !== "_" ? Result.throw(state) : Parser.peek(s => Parser.any(s)
              .then((t, err) => !/[a-zA-Z_0-9\(\):=;\\.\-> \r\n]/.test(t.data) ? { ...t, fail: "_" } :
                pred(t) ? t : err({ ...t, fail: msg ?? "_Satisfy" })))(state)
              .then((s, err) => s.fail !== "_" ? s :
                (this.setPos({ start: state.pos, end: s.pos }), err({ ...state, fail: `Found illegal character "${s.data}"` }))) },

          cut (p, msg, newPos) { return s => p(s).catch(e =>
            Parser.cut(Result.throw, e.fail[0] === "_" ? msg : undefined, this.setPos(newPos ?? { start: s.pos, end: e.pos }))(e)) },
          parens (p) { return Parser.do([ Parser.char("("),
            ({}, s) => Parser.seq([ Parser.option(this.ws), p ])(s),
            (x, y, s) => Parser.seq([ this.cut(Parser.char(")"), "Unclosed parens", { start: x.pos, end: y.pos }),
              s1 => Parser.option(this.ws)(s1).then(s2 => (({ ...s2, data: s.data }))) ])(s) ]) },
          symbol (str, isTest = true) { return state => Parser.map(Parser.guard(
            Parser.many((isTest ? this : Parser).satisfy(s => s.data === str[s.offset - state.offset - 1], `Symbol: "${str}"`)),
            data => data.length === str.length), data => data.join(""))(state) },
          catchSymbol (p) { return state => p(state).catch((s, err) => s.fail[0] === "_" ? err(s) :
            Parser.mapFull(Parser.many(Parser.satisfy(t => /[^ \(\)\r\n]/.test(t.data))),
              t => { this.setPos({ start: state.pos, end: t.pos, writable: false });
                return err({ ...t, data: t.data.join(""), fail: s.fail }) })(s)) },
          keyword (str) { return state => Parser.seq([ this.symbol(str), s1 => Parser.option(this.ws)(s1)
            .then(s2 => (this.setPos({ start: state.pos, end: s1.pos }), { ...s2, data: s1.data })) ])(state) },
          keyword_ (str) { return state => Parser.seq([ this.symbol(str), s1 => this.ws(s1)
            .then(s2 => (this.setPos({ start: state.pos, end: s1.pos }), { ...s2, data: s1.data })) ])(state) },
          ident (state) { return this.catchSymbol(Parser.reqr(Parser.seq([
            this.satisfy(s => /[a-zA-Z_]/.test(s.data)),
            Parser.do([ Parser.alt(Parser.many(this.satisfy(s => /[a-zA-Z_0-9]/.test(s.data))), s => ({ ...s, data: [] })),
              (s, t) => (this.setPos({ start: state.pos, end: t.pos }), { ...t, data: s.data + t.data.join("") }) ]) ]), Parser.option(this.ws)))(state) },

          atom (state) { return Parser.choice([
            Parser.mapFull(Parser.guard(this.ident, data => !~["let", "U", "_"].findIndex(x => x === data)),
              s => (this.setPos({ start: state.pos }), { ...s, data: new this.RVar(s.data, gctx.pos) })),
            Parser.mapFull(this.keyword("U"), s => ({ ...s, data: new this.RU(gctx.pos) })),
            Parser.mapFull(this.keyword("_"), s => ({ ...s, data: new this.RHole(gctx.pos) })),
            this.parens(this.term) ])(state) },

          binder (state) { return Parser.map(this.catchSymbol(Parser.alt(this.ident, this.keyword("_"))), data => [ data, gctx.pos ])(state) },
          spine (state) { return Parser.map(Parser.many(this.atom),
            data => (this.setPos({ start: state.pos }), data.reduce((acc, atom) => new this.RApp(acc, atom, this.setPos({ end: atom.pos[1] })))))(state) },

          lam (state) { return Parser.do([ this.keyword("\\"),
            ({}, s) => Parser.many(this.binder)(s),
            (x, y, s) => Parser.seq([ this.cut(this.keyword("."), "Lambda without body", { start: x.pos, end: y.pos }), this.term ])(s),
            ({}, {}, s, t) => ({ ...t, data: s.data.reduceRight((acc, [b, pos]) =>
              new this.RLam(b, acc, this.setPos({ start: pos[1] })), t.data) }) ])(state) },

          namedPi (state) { return Parser.seq([
            Parser.many(this.parens(Parser.seq([ Parser.many(this.binder),
              Parser.do([ Parser.seq([ this.keyword(":"), this.term ]),
                (s, t) => ({ ...t, data: s.data.map(([b, pos]) => [b, t.data, [ pos[0], t.data.pos[1] ]]) }) ]) ]))),
            Parser.do([ Parser.seq([ this.cut(this.catchSymbol(this.keyword("->")), "Expected function type arrow"), this.term ]),
              (s, t) => ({ ...t, data: s.data.flat(1).reduceRight((acc, [b, tm, pos]) =>
                new this.RPi(b, tm, acc, this.setPos({ start: pos[0] })), t.data) }) ]) ])(state).then(s => (this.setPos({ start: state.pos }), s)) },
          anonPiOrSpine (state) { return Parser.seq([ this.cut(this.spine, "Malformed spine", {}),
            Parser.option(Parser.do([ Parser.reql(this.keyword("->"), this.cut(this.catchSymbol(this.term), "Malformed term", {})),
              (s, t) => ({ ...t, data: new this.RPi("_", s.data, t.data, this.setPos({ start: state.pos })) }) ])) ])(state) },

          let (state) { return Parser.seq([ this.keyword_("let"), this.cut(Parser.map(this.binder, ([b]) => b), "Malformed binder", {}),
            Parser.do([ Parser.seq([ this.cut(this.keyword(":"), 'Let missing ":"'), this.term ]),
              ({}, s) => Parser.seq([ this.cut(this.keyword("="), 'Let missing "="'), this.term ])(s),
              ({}, {}, s) => Parser.seq([ this.cut(this.keyword(";"), 'Let missing ";"'),
                this.cut(this.term, "Definition list must end with term expression") ])(s),
              (s, t, u, v) => ({ ...v, data: new this.RLet(s.data, t.data, u.data, v.data, this.setPos({ start: state.pos })) }) ]) ])(state) },
            
          term (state) { return Parser.choice([ this.lam, this.let, this.namedPi, this.anonPiOrSpine ])(state) },
          parse (state) {
            ctx.source = state.source;
            debug.log("Parse:");
            return Parser.seq([ Parser.option(this.ws), this.cut(Parser.reqr(this.term, Parser.eof), "No expression found", {}) ])(state)
              .catch(this.displayError)
              .then(state => (console.log(`${state.data}`), { data: state.data })) },
          displayError ({ fail }, err) {
            Object.defineProperty(gctx, "pos", { writable: true });
            let lines = ctx.source.split(/\r\n?|\n/);
            return err({ fail: fail[0] === "_" ? fail : `Parser error: ${fail}\n${lines[gctx.pos[0][0] - 1]}\n${"-".repeat(gctx.pos[0][1] - 1)}${
              "^".repeat((gctx.pos[1][1] - gctx.pos[0][1]) || 1)} ${gctx.pos.join("-")}` }) }
        }),

        evaluatorData: [ ({ local: ctx, global: gctx }) => ({
          eval: Evaluator.match({
            var ({ term, env }) { return env[env.length - term.ix - 1] },
            app ({ term, env }) { return this.vApp({ vfunc: this.eval({ term: term.func, env }), varg: this.eval({ term: term.arg, env }) }) },
            lam ({ term, env }) { return new this.VLam(term.name, { term: term.body, env }) },
            pi ({ term, env }) { return new this.VPi(term.name, this.eval({ term: term.dom, env }), { term: term.cod, env }) },
            let ({ term, env }) { return this.eval.withContext({ names: [term.name].concat(ctx.names) },
              [ { term: term.next, env: env.concat([ this.eval({ env, term: term.term }) ]) } ]) },
            u () { return new this.VU() },
            meta ({ term }) { return this.vMeta({ mvar: term.mvar }) },
            insmeta ({ term, env }) { return this.vAppBDs({ env, val: this.vMeta({ mvar: term.mvar }), bds: term.bds }) }
          }, { scrut: [ "term" ] }),
          cApp ({ cls: { term, env }, val }) { return this.eval({ term, env: env.concat([ val ]) }) },
          vApp: Evaluator.match({
            vlam ({ vfunc, varg }) { return this.cApp({ cls: vfunc.cls, val: varg }) },
            vflex ({ vfunc, varg }) { return new this.VFlex(vfunc.mvar, vfunc.spine.concat([ varg ])) },
            vrigid ({ vfunc, varg }) { return new this.VRigid(vfunc.lvl, vfunc.spine.concat([ varg ])) },
          }, { scrut: [ "vfunc" ] }),
          vAppSp ({ val, spine }) { return spine.reduce((acc, v) => this.vApp({ vfunc: acc, varg: v }), val) },
          vMeta ({ mvar }) { let e = gctx.metas.get(mvar); return e === null ? new this.VFlex(mvar, []) : e },
          vAppBDs ({ env, val, bds }) { return bds.reduce((acc, bd, i) => bd ? this.vApp({ vfunc: acc, varg: env[i] }) : acc, val) },
          
          quote: Evaluator.match({
            vflex ({ lvl, val }) { return this.quoteSp({ lvl, term: new this.Meta(val.mvar), spine: val.spine }) },
            vrigid ({ lvl, val }) { return this.quoteSp({ lvl, term: new this.Var(lvl - val.lvl - 1), spine: val.spine }) },
            vlam ({ lvl, val }) { return new this.Lam(val.name,
              this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VRigid(lvl, []) }) })) },
            vpi ({ lvl, val }) { return new this.Pi(val.name, this.quote({ lvl, val: val.dom }),
              this.quote({ lvl: lvl + 1, val: this.cApp({ cls: val.cls, val: new this.VRigid(lvl, []) }) })) },
            vu () { return new this.U() }
          }, { scrut: [ "val" ] }),
          quoteSp ({ lvl, term, spine }) { return spine.reduce((acc, val) => new this.App(acc, this.quote({ lvl, val })), term) },
          force ({ val }) { if (val.constructor.name === "VFlex") {
            let e = gctx.metas.get(val.mvar);
            if (e !== null) return this.force({ val: this.vAppSp({ val: e, spine: val.spine }) })
          } return val },

          nextMeta: (i => () => i++)(0),
          freshMeta () {
            let m = this.nextMeta();
            gctx.metas.set(m, null);
            return new this.InsMeta(m, ctx.bds) },
          
          liftPRen ({ dom, cod, ren }) { return { dom: dom + 1, cod: cod + 1, ren: ren.set(cod, dom) } },
          invertPRen ({ lvl, spine }) { return spine.reduce((acc, val) => acc.then(([ dom, ren ], err) =>
            (fval => fval.constructor.name === "VRigid" && !ren.has(fval.lvl) ?
              [ dom + 1, ren.set(fval.lvl, dom) ] : err({ msg: "Unification error: occurs check" }))(this.force({ val }))),
            Result.pure([ 0, new Map() ])).then(([ dom, ren ]) => ({ dom, cod: lvl, ren })) },
          rename: Evaluator.match({
            vflex ({ mvar, pren, fval }) { return mvar === fval.mvar ? Result.throw({ message: "Unification error" }) :
              fval.spine.reduce((acc, val) => acc.then(accTerm => this.rename({ mvar, pren, val })
                .then(term => new this.App(accTerm, term))), Result.pure(new this.Meta(fval.mvar))) },
            vrigid ({ mvar, pren, fval }) { return !pren.ren.has(fval.lvl) ? Result.throw({ msg: "Unification error: variable escapes scope" }) :
              fval.spine.reduce((acc, val) => acc.then(accTerm => this.rename({ mvar, pren, val })
                .then(term => new this.App(accTerm, term))), Result.pure(new this.Var(pren.dom - pren.ren.get(fval.lvl) - 1))) },
            vlam ({ mvar, pren, fval }) { return this.rename({ mvar, pren: this.liftPRen(pren),
              val: this.cApp({ cls: fval.cls, val: new this.VRigid(pren.cod, []) }) })
              .then(body => new this.Lam(fval.name, body)) },
            vpi ({ mvar, pren, fval }) { return this.rename({ mvar, pren, val: fval.dom })
                .then(dom => this.rename({ mvar, pren: this.liftPRen(pren),
                  val: this.cApp({ cls: fval.cls, val: new this.VRigid(pren.cod, []) }) })
                  .then(cod => new this.Pi(fval.name, dom, cod))) },
            vu () { return Result.pure(new this.U()) }
          }, { scrut: [ { fval ({ val }) { return this.force({ val }) } } ] }),

          solve ({ lvl, mvar, spine, val }) { return this.invertPRen({ lvl, spine })
            .then(pren => this.rename({ mvar, pren, val })
              .then(rhs => { gctx.metas.set(mvar,
                this.eval({ term: (tm => { for (let i = pren.dom; i > 0; i--)
                  tm = new this.Lam(`x${i}`, tm); return tm })(rhs), env: [] })) })) },
          unify: Evaluator.match({
            "vlam _" ({ lvl, fval0, fval1 }) { return fval1.constructor.name === "VLam" ? this.unify({ lvl: lvl + 1,
              val0: this.cApp({ cls: fval0.cls, val: new this.VRigid(lvl, []) }), val1: this.cApp({ cls: fval1.cls, val: new this.VRigid(lvl, []) }) }) :
              this.unify({ lvl: lvl + 1, val0: this.cApp({ cls: fval0.cls, val: new this.VRigid(lvl, []) }),
                val1: this.vApp({ vfunc: fval1, varg: new this.VRigid(lvl, []) }) }) },
            "vpi vpi" ({ lvl, fval0, fval1 }) { return this.unify({ lvl, val0: fval0.dom, val1: fval1.dom })
              .then(() => this.unify({ lvl: lvl + 1,
                val0: this.cApp({ cls: fval0.cls, val: new this.VRigid(lvl, []) }), val1: this.cApp({ cls: fval1.cls, val: new this.VRigid(lvl, []) }) })) },
            "vu vu" () { return Result.pure() },
            "vrigid vrigid" ({ lvl, fval0, fval1 }) { return fval0.lvl === fval1.lvl ? this.unifySp({ lvl, sp0: fval0.spine, sp1: fval1.spine }) :
              Result.throw({ msg: "Unification error: rigid mismatch" }) },
            "vflex _" ({ lvl, fval0, fval1 }) { return fval1.constructor.name === "VFlex" && fval0.mvar === fval1.mvar ?
              this.unifySp({ lvl, sp0: fval0.spine, sp1: fval1.spine }) : this.solve({ lvl, mvar: fval0.mvar, spine: fval0.spine, val: fval1 }) },
            "_" ({ lvl, fval0, fval1 }) { return fval1.constructor.name === "VLam" ? this.unify({ lvl: lvl + 1,
              val0: this.vApp({ vfunc: fval0, varg: new this.VRigid(lvl, []) }), val1: this.cApp({ cls: fval1.cls, val: new this.VRigid(lvl, []) }) }) :
              fval1.constructor.name === "VFlex" ? this.solve({ lvl, mvar: fval1.mvar, spine: fval1.spine, val: fval0 }) :
                Result.throw({ msg: "Unification error: rigid mismatch" }) }
          }, { scrut: [ { fval0 ({ val0 }) { return this.force({ val: val0 }) } }, { fval1 ({ val1 }) { return this.force({ val: val1 }) } } ] }),
          unifySp ({ lvl, sp0, sp1 }) { if (sp0.length !== sp1.length) return Result.throw({ msg: "Unification error: rigid mismatch" })
            else return sp0.reduce((acc, val0, i) => acc.then(() => this.unify({ lvl, val0, val1: sp1[i] })), Result.pure()) },


          bind ({ name, vtype }) { return { ...ctx,
            env: ctx.env.concat([ new this.VRigid(ctx.lvl, []) ]),
            types: ctx.types.concat([[ name, vtype ]]), names: [name].concat(ctx.names),
            lvl: ctx.lvl + 1, bds: ctx.bds.concat([1]) } },
          define ({ name, val, vtype }) { return { ...ctx,
            env: ctx.env.concat([ val ]),
            types: ctx.types.concat([[ name, vtype ]]),
            lvl: ctx.lvl + 1, bds: ctx.bds.concat([0]) } },
          closeVal ({ val }) { return { term: this.quote({ val, lvl: ctx.lvl + 1 }), env: ctx.env } },
          unifyCatch ({ val0, val1 }) { return this.unify({ lvl: ctx.lvl, val0, val1 }).catch((e, err) => e.msg.slice(0, 17) !== "Unification error" ? err(e) :
            err({ msg: `${e.msg}\nCan't unify\n    ${this.quote({ lvl: ctx.lvl, val: val0 })}\nwith\n    ${this.quote({ lvl: ctx.lvl, val: val1 })}\n` })) },
          check: Evaluator.match({
            "rlam vpi" ({ rterm, vtype }) { return this.check.withContext(this.bind({ name: rterm.name, vtype: vtype.dom }),
              [ { rterm: rterm.body, vtype: this.cApp.withContext({ names: [rterm.name].concat(ctx.names) }, [ { cls: vtype.cls, val: new this.VRigid(ctx.lvl, []) } ]) } ], res => res
                .then(body => new this.Lam(rterm.name, body))) },
            "rlet _" ({ rterm, vtype }) { return this.check({ rterm: rterm.type, vtype: new this.VU() })
              .then(type => {
                let cvtype = this.eval({ term: type, env: ctx.env });
                return this.check({ rterm: rterm.term, vtype: cvtype })
                  .then(term => this.check.withContext(define({ name: term.name, val: this.eval({ term, env: ctx.env }), vtype: cvtype }),
                    [ { rterm: rterm.next, vtype } ], res => res
                      .then(next => this.Let(rterm.name, type, term, next)))) }) },
            "rhole _" () { return Result.pure(this.freshMeta()) },
            _ ({ rterm, vtype }) { return this.infer({ rterm })
              .then(({ term, vtype: ivtype }) => this.unifyCatch({ lvl: ctx.lvl, val0: vtype, val1: ivtype }).then(() => term)) }
          }, { decorate: ({ rterm }) => gctx.pos = rterm.pos, scrut: [ "rterm", "vtype" ] }),
          infer: Evaluator.match({
            rvar ({ rterm }) { return (ix => ~ix ? Result.pure({ term: new this.Var(ctx.lvl - ix - 1), vtype: ctx.types[ix][1] }) :
              Result.throw({ msg: `Evaluator error: Name not in scope "${rterm.name}"` }))(ctx.types.findLastIndex(([n]) => n === rterm.name)) },
            rlam ({ rterm }) { let vtype = this.eval({ cls: ctx.env, val: this.freshMeta() });
              return this.infer.withContext(this.bind({ name: rterm.name, vtype }), [ { rterm: rterm.cls } ], res => res
                .then(({ term, vtype: ivtype }) => ({ term: new this.Lam(rterm.name, term),
                  vtype: new this.VPi(rterm.name, vtype, this.closeVal({ val: ivtype })) }))) },
            rapp ({ rterm }) { return this.infer({ rterm: rterm.func }).then(({ term, vtype }) => (fvtype => {
              if (fvtype.constructor.name === "VPi") return Result.pure([ fvtype.dom, fvtype.cls ]);
              else { let dom = this.eval({ env: ctx.env, term: this.freshMeta() });
                return this.freshMeta.withContext(this.bind({ name: "x", vtype: dom }), []).then(im => ({ term: im, env: ctx.env }))
                  .then(cls => this.unifyCatch({ val0: new this.VPi("x", dom, cls), val1: vtype }).then(() => [ dom, cls ])) } })(this.force({ val: vtype }))
              .then(([ dom, cls ]) => this.check({ rterm: rterm.arg, vtype: dom })
                .then(arg => ({ term: new this.App(term, arg), vtype: this.cApp({ cls, val: this.eval({ env: ctx.env, term: arg }) }) })))) },
            ru () { return Result.pure({ term: new this.U(), vtype: new this.VU() }) },
            rpi ({ rterm }) { return this.check({ rterm: rterm.dom, vtype: new this.VU() })
              .then(dom => this.check.withContext(this.bind({ name: rterm.name, vtype: this.eval({ env: ctx.env, term: dom }) }),
                [ { rterm: rterm.cod, vtype: new this.VU() } ], res => res.then(cod => ({ term: new this.Pi(rterm.name, dom, cod), vtype: new this.VU() })))) },
            rlet ({ rterm }) { return this.check({ rterm: rterm.type, vtype: new this.VU() }).then(type => {
              let cvtype = this.eval({ term: type, env: ctx.env });
              return this.check({ rterm: rterm.term, vtype: cvtype })
                .then(term => this.infer.withContext(this.define({ name: rterm.name, val: this.eval({ term, env: ctx.env }), vtype: cvtype }),
                  [ { rterm: rterm.next } ], res => res.then(({ term: next, vtype }) => ({ term: new this.Let(rterm.name, type, term, next), vtype })))) }) },
            rhole () { return { vtype: this.eval({ env: ctx.env, term: this.freshMeta() }), term: this.freshMeta() } }
          }, { decorate: ({ rterm }) => gctx.pos = rterm.pos, scrut: [ "rterm" ] }),

          doElab ({ rterm }) { return this.infer({ rterm }).catch(this.displayError) },
          nf ({ data: rterm }) {
            debug.log("Expression normal form:");
            return this.doElab({ rterm })
              .then(({ term, vtype }) => ({
                term: this.quote({ lvl: 0, val: this.eval({ term, env: [] }) }),
                type: this.quote({ lvl: 0, val: vtype }) })) },
          type ({ data: rterm }) {
            debug.log("Expression type:");
            return this.doElab({ rterm })
              .then(({ vtype }) => ({ type: this.quote({ lvl: 0, val: vtype }) })) },
          elab ({ data: rterm }) {
            debug.log("Elaborate expression:");
            return this.doElab({ rterm })
              .then(({ term }) => ({ term, metas: Array.from(gctx.metas)
                .map(([m, e]) => `let ?${m} = ${e === null ? "?" : this.quote({ lvl: 0, val: e }) };`).join("\n") })) },
          displayError ({ msg }, err) {
            let lines = ctx.source.split(/\r\n?|\n/);
            return err({ message: `${msg}\n${lines[gctx.pos[0][0] - 1]}\n${"-".repeat(gctx.pos[0][1] - 1)}${
              "^".repeat(gctx.pos[1][1] - gctx.pos[0][1])} ${gctx.pos.join("-")}` }) }
        }), "nf", "type", "elab" ]
      });

  let dtimp = new Context({
    debugHandler: p => ({}, prop) => p !== true && p !== dtimp.phase ? () => {} :
      prop === "log" ? (v, ...rest) => {
        let declutter = v => { if (v?.hasOwnProperty("source")) { let { source, ...o } = v; return [o] } else return [v] };
        console.log(...(typeof v === "string" ? [v] : declutter(v)), ...rest.flatMap(declutter)
          .flatMap((o, i) => [ ...(i === 0 ? ["|"] : []), "{",
            ...Object.entries(o).flatMap(([k, v], i, ar) => [`${k}:`,
              typeof v === "string" ? `\`${v}\`` : AST.tag.isPrototypeOf(v?.constructor) ? `${v}` : v, ...(i === ar.length - 1 ? [] : [","])]), "}"]),
          (stack => { try { throw new Error('') } catch (e) { stack = e.stack || "" }
            return stack.split(`\n`)[5].replace(/@.*(js)/g, "") })()) } : console[prop],
    
    contextData: {
      local: { env: [], types: [], bds: [], lvl: 0, pos: 0, names: [] },
      global: { metas: new Map(), pos: [], source: "" } },

    astData: ({ local: ctx }) => ({}),

    parserData: ({ local: ctx, global: gctx }) => ({
      parse () {}
    }),

    evaluatorData: [ ({ local: ctx, global: gctx }) => ({
      nf () {},
      type () {},
      elab () {}
    }), "nf", "type", "elab" ],
  });

  const sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  return Object.defineProperties({}, {
    import: { get() {
      return (opt = {}) => sequence(() => new Promise((ok, err) => {
        if ("code" in opt && !("path" in opt)) ok(opt.code);
        else if ("path" in opt) fetch(opt.path).then(rsp => rsp.text()).then(ok);
        else err({ message: "Load error: option object malformed or missing" });
      }).then(src => ({ ready: (tts => tts.reduce((acc1, [tt, meths], i) => Object.assign(acc1, { [i + 1]:
        meths.reduce((acc2, meth) => Object.assign(acc2, { [meth]: { run: () => tt.parse(src).then(tt[meth]).toPromise() } }), {})  }), {}))
      ([[ulc, ["nf"]],
        [dt, ["nf", "type"]],
        [dth, ["nf", "type", "elab"]],
        [dtimp, ["nf", "type", "elab"]]])[which ?? 1] })))
    } },
    select: { get() { return i => which = i } }
  })
}