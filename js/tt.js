var TT = (options = {}) => {
  let { debug, which } = options;
  debug = debug ? console : new Proxy({}, { get() { return () => {} } });
  
  class Result {  // Error handling
    constructor (fn) {
      let thrown = false, value = null, error = v => (thrown = true, v),
          join = (fn, v = value) => (r => { Result.prototype.isPrototypeOf(r) &&
            (x => value = "ok" in x ? x.ok : error(x.err))(r.unwrap());
              debug.log(`{ ${Object.keys(value).map(k => `${k}: "${value[k]}"`).join(", ")} }`); })
            (value = fn(v, error));
      this.then = fn => (thrown || join(fn), this);  // On resolve
      this.catch = fn => (thrown && (thrown = false, join(fn)), this);  // On reject
      this.unwrap = () => ({ [ thrown ? "err" : "ok" ]: value });  // Await
      this.toPromise = () => new Promise((ok, err) => this.then(s => ok(s)).catch(e => err(e)));
      return fn(v => join(() => v), e => join(() => error(e)))
    }
    static pure (v) { return new Result(r => r(v)) }  // Resolve
    static throw (e) { return new Result((_, l) => l(e)) }  // Reject
  }

  class RVar {
    constructor (n) { this.ix = n }
    toString () { return `${this.ix}` }
  }
  class RApp {
    constructor (f, a) { this.func = f; this.arg = a }
    toString (prec = false) { return (str => prec ? `(${str})` : str)
      (this.func.constructor.name === "RApp" ?
        `${this.func.func.toString(false)} ${this.func.arg.toString(true)} ${this.arg.toString(true)}` :
        `${this.func.toString(true)} ${this.arg.toString(true)}`) }
  }
  class RLam {
    constructor (b) { this.body = b }
    toString (prec = false) { return (str => prec ? `(${str})` : str)
      (`\\ ${this.body.toString(false)}`) }
  }
  class RLet {
    constructor (tm, nx) { this.term = tm; this.next = nx }
    toString () { return `let ${this.term.toString(false)};\n${this.next.toString(false)}` }
  }

  class VVar { constructor (n) { this.lvl = n } }
  class VApp { constructor (f, a) { this.func = f; this.arg = a } }
  class VLam { constructor (e) { this.env = e } }

  class Parser {
    static seq (ps) { return state => ps.reduce((acc, p) => acc.then(p), Result.pure(state)) }
    static do (ps) { return state =>
      ps.reduce((acc, p) => (...ss) => acc(...ss).then(s => p(...ss, s)), Result.pure)(state) }
    static reql (p1, p2) { return state => p1(state).then(s1 => p2({ ...s1, data: state.data })) }
    static reqr (p1, p2) { return state => p1(state).then(s1 => p2(s1).then(s2 => ({ ...s2, data: s1.data }))) }
    static map (p, fn) { return state => p(state).then(s => ({ ...s, data: fn(s.data) })) }
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
      .then((s, err) => pred(s) ? s : err({ ...s, fail: msg || "_Satisfy" }))) }
    static char (c) { return Parser.satisfy(s => s.data === c, `_Char ${c}`) }
    static many (p) { return Parser.cut(state => ((loop = (s, res) => p(s)
      .then(st => loop(st, res.concat([st.data])))
      .catch(({ fail, ...st }, err) => res.length ?
        ({ ...st, data: res }) : err({ ...st, fail }))) => loop(state, []))(), "Many") }
    static scan (pred, msg) { return state => Parser.many(s1 => Parser.any(s1).then((s2, err) => 
      s2.source.length <= s2.offset ? err({ ...state, fail: msg || "_Scan" }) :
        !pred(s2) ? s2 : err({ ...s2, fail: "_" })))(state)
      .catch((s3, err) => s3.fail === "_" ? err(s3) : s3) }
    
    constructor ({ parse, ...cmb }) {
      for (let k in { parse, ...cmb })
        cmb[k] = (f => function () {
          debug.group(k);
          let res = f.apply(cmb, arguments);
          debug.groupEnd();
          return res
        })(cmb[k]);
      this.parse = source => Result.pure({ source, offset: 0, pos: [1, 1], data: null })
        .then(parse.bind(cmb))
        .then(state => state.data)
        .catch((e, err) => err(e.fail[0] === "_" ? "Unmanaged parser error" : e.fail))
    }
  }

  class Evaluator {
    static debug (sw) {
      for (let k in sw) sw[k] = (f => function () { debug.log(k); return f() })(sw[k]);
      return sw
    }
    constructor ({ nf, ...fns }) {
      for (let k in { nf, ...fns })
        fns[k] = (f => function (...args) {
          debug.group(k, ...args);
          let res = f.apply(fns, args);
          debug.groupEnd();
          return res
        })(fns[k]);
      this.nf = term => Result.pure({ term, ctx: [] })
        .then(nf.bind(fns))
    }
  }

  let deBruijnClosures1 = new Parser({
        ws (state) { return Parser.many(Parser.choice([
          Parser.satisfy(s => /[^\S\r\n]/g.test(s.data), "_HWS"),
          Parser.satisfy(s => /\r\n?|\n/g.test(s.data), "_VWS"),
          st => this.symbol(Parser.satisfy(s => s.data === "--"[s.offset - state.offset - 1], "_Comment"))(st)
            .then(Parser.scan(s => /\r\n?|\n/g.test(s.data), "_Comment"))
        ]))(state) },
        symbol (p) { return Parser.many(p) },
        parens (p) { return state => Parser.reql(
          Parser.seq([ Parser.char("("), Parser.option(this.ws) ]),
          Parser.reqr(p, Parser.char(")")))(state) },
        keyword (str) { return state => Parser.map(Parser.reqr(
          this.symbol(Parser.satisfy(s => s.data === str[s.offset - state.offset - 1], "_Keyword: " + str)),
          this.ws), data => data.join(""))(state) },

        ix (state) { return this.symbol(Parser.satisfy(s => /\d/g.test(s.data), "_Index"))(state) },
        atom (state) { return Parser.reqr(Parser.alt(
          Parser.map(this.ix, data => new RVar(parseInt(data))),
          this.parens(this.term)), Parser.option(this.ws))(state) },
        spine (state) { return Parser.map(Parser.many(this.atom),
          data => data.reduce((acc, atom) => new RApp(acc, atom)))(state) },

        lam (state) { return Parser.seq([ this.keyword("\\"),  // Allow "\0" ?
          Parser.map(this.term, data => new RLam(data)) ])(state) },
        let (state) { return Parser.seq([ this.keyword("let"), this.term,
          Parser.do([ Parser.seq([ this.keyword(";"), this.term ]),
            (t, u) => ({ ...u, data: new RLet(t.data, u.data) }) ]) ])(state) },

        term (state) { return Parser.choice([ this.lam, this.let, this.spine ])(state) },
        parse (state) {
          debug.log("Parse:");
          return Parser.seq([ Parser.option(this.ws), Parser.reqr(this.term, Parser.eof) ])(state)
        }
      }),
      untypedLC = new Evaluator({
        eval ({ term, ctx }) { return Evaluator.debug({
          rvar: () => ctx[ctx.length - term.ix - 1],
          rapp: () => ((func, arg) => func.constructor.name === "VLam" ?
            this.cApp(func.env, arg) : new VApp(func, arg))
            (this.eval({ ctx, term: term.func }), this.eval({ ctx, term: term.arg })),
          rlam: () => new VLam({ term: term.body, ctx }),
          rlet: () => this.eval({ term: term.next, ctx: ctx.concat([this.eval({ ctx, term: term.term })]) })
        })[term.constructor.name.toLowerCase()]() },

        cApp ({ term, ctx }, val) { return this.eval({ term, ctx: ctx.concat([val]) }) },

        quote (lvl, val) { return Evaluator.debug({
          vvar: () => new RVar(lvl - val.lvl - 1),
          vapp: () => new RApp(this.quote(lvl, val.func), this.quote(lvl, val.arg)),
          vlam: () => new RLam(this.quote(lvl + 1, this.cApp(val.env, new VVar(lvl))))
        })[val.constructor.name.toLowerCase()]() },

        nf (env) {
          debug.log("Normal form:");
          return { term: this.quote(env.ctx.length, this.eval(env)) }
        }
      });

  const sequence = (p => fn => p = fn ? p.then(fn) : p)(Promise.resolve());
  return Object.defineProperties({}, {
    import: { get() {
      return opt => sequence(() => new Promise((ok, err) => {
        opt ??= {};
        if ("code" in opt && !("path" in opt)) ok(opt.code);
        else if ("path" in opt) fetch(opt.path).then(rsp => rsp.text()).then(ok);
        else err(new Error("Load error: option object malformed or missing"));
      }).then(({
        1: src => deBruijnClosures1.parse(src).then(untypedLC.nf).toPromise(),
        2: () => ({ term: "TBD" })
      })[which ?? 1])
        .then(result => ({ context: { definitions: result.term } })))
    } },
    select: { get() { return i => which = i } }
  })
}