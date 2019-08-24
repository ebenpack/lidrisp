(function(f){if(typeof exports==="object"&&typeof module!=="undefined"){module.exports=f()}else if(typeof define==="function"&&define.amd){define([],f)}else{var g;if(typeof window!=="undefined"){g=window}else if(typeof global!=="undefined"){g=global}else if(typeof self!=="undefined"){g=self}else{g=this}g.lidrisp = f()}})(function(){var define,module,exports;return (function(){function r(e,n,t){function o(i,f){if(!n[i]){if(!e[i]){var c="function"==typeof require&&require;if(!f&&c)return c(i,!0);if(u)return u(i,!0);var a=new Error("Cannot find module '"+i+"'");throw a.code="MODULE_NOT_FOUND",a}var p=n[i]={exports:{}};e[i][0].call(p.exports,function(r){var n=e[i][1][r];return o(n||r)},p,p.exports,r,e,n,t)}return n[i].exports}for(var u="function"==typeof require&&require,i=0;i<t.length;i++)o(t[i]);return o}return r})()({1:[function(require,module,exports){
(function (process,Buffer){
"use strict";

(function(){

const $JSRTS = {
    throw: function (x) {
        throw x;
    },
    Lazy: function (e) {
        this.js_idris_lazy_calc = e;
        this.js_idris_lazy_val = void 0;
    },
    force: function (x) {
        if (x === undefined || x.js_idris_lazy_calc === undefined) {
            return x
        } else {
            if (x.js_idris_lazy_val === undefined) {
                x.js_idris_lazy_val = x.js_idris_lazy_calc()
            }
            return x.js_idris_lazy_val
        }
    },
    prim_strSubstr: function (offset, len, str) {
        return str.substr(Math.max(0, offset), Math.max(0, len))
    }
};
$JSRTS.os = require('os');
$JSRTS.fs = require('fs');
$JSRTS.prim_systemInfo = function (index) {
    switch (index) {
        case 0:
            return "node";
        case 1:
            return $JSRTS.os.platform();
    }
    return "";
};
$JSRTS.prim_writeStr = function (x) { return process.stdout.write(x) }
$JSRTS.prim_readStr = function () {
    var ret = '';
    var b = new Buffer(1024);
    var i = 0;
    while (true) {
        $JSRTS.fs.readSync(0, b, i, 1)
        if (b[i] == 10) {
            ret = b.toString('utf8', 0, i);
            break;
        }
        i++;
        if (i == b.length) {
            var nb = new Buffer(b.length * 2);
            b.copy(nb)
            b = nb;
        }
    }
    return ret;
};
$JSRTS.jsbn = (function () {

  // Copyright (c) 2005  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Basic JavaScript BN library - subset useful for RSA encryption.

  // Bits per digit
  var dbits;

  // JavaScript engine analysis
  var canary = 0xdeadbeefcafe;
  var j_lm = ((canary & 0xffffff) == 0xefcafe);

  // (public) Constructor
  function BigInteger(a, b, c) {
    if (a != null)
      if ("number" == typeof a) this.fromNumber(a, b, c);
      else if (b == null && "string" != typeof a) this.fromString(a, 256);
      else this.fromString(a, b);
  }

  // return new, unset BigInteger
  function nbi() { return new BigInteger(null); }

  // am: Compute w_j += (x*this_i), propagate carries,
  // c is initial carry, returns final carry.
  // c < 3*dvalue, x < 2*dvalue, this_i < dvalue
  // We need to select the fastest one that works in this environment.

  // am1: use a single mult and divide to get the high bits,
  // max digit bits should be 26 because
  // max internal value = 2*dvalue^2-2*dvalue (< 2^53)
  function am1(i, x, w, j, c, n) {
    while (--n >= 0) {
      var v = x * this[i++] + w[j] + c;
      c = Math.floor(v / 0x4000000);
      w[j++] = v & 0x3ffffff;
    }
    return c;
  }
  // am2 avoids a big mult-and-extract completely.
  // Max digit bits should be <= 30 because we do bitwise ops
  // on values up to 2*hdvalue^2-hdvalue-1 (< 2^31)
  function am2(i, x, w, j, c, n) {
    var xl = x & 0x7fff, xh = x >> 15;
    while (--n >= 0) {
      var l = this[i] & 0x7fff;
      var h = this[i++] >> 15;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x7fff) << 15) + w[j] + (c & 0x3fffffff);
      c = (l >>> 30) + (m >>> 15) + xh * h + (c >>> 30);
      w[j++] = l & 0x3fffffff;
    }
    return c;
  }
  // Alternately, set max digit bits to 28 since some
  // browsers slow down when dealing with 32-bit numbers.
  function am3(i, x, w, j, c, n) {
    var xl = x & 0x3fff, xh = x >> 14;
    while (--n >= 0) {
      var l = this[i] & 0x3fff;
      var h = this[i++] >> 14;
      var m = xh * l + h * xl;
      l = xl * l + ((m & 0x3fff) << 14) + w[j] + c;
      c = (l >> 28) + (m >> 14) + xh * h;
      w[j++] = l & 0xfffffff;
    }
    return c;
  }
  var inBrowser = typeof navigator !== "undefined";
  if (inBrowser && j_lm && (navigator.appName == "Microsoft Internet Explorer")) {
    BigInteger.prototype.am = am2;
    dbits = 30;
  }
  else if (inBrowser && j_lm && (navigator.appName != "Netscape")) {
    BigInteger.prototype.am = am1;
    dbits = 26;
  }
  else { // Mozilla/Netscape seems to prefer am3
    BigInteger.prototype.am = am3;
    dbits = 28;
  }

  BigInteger.prototype.DB = dbits;
  BigInteger.prototype.DM = ((1 << dbits) - 1);
  BigInteger.prototype.DV = (1 << dbits);

  var BI_FP = 52;
  BigInteger.prototype.FV = Math.pow(2, BI_FP);
  BigInteger.prototype.F1 = BI_FP - dbits;
  BigInteger.prototype.F2 = 2 * dbits - BI_FP;

  // Digit conversions
  var BI_RM = "0123456789abcdefghijklmnopqrstuvwxyz";
  var BI_RC = new Array();
  var rr, vv;
  rr = "0".charCodeAt(0);
  for (vv = 0; vv <= 9; ++vv) BI_RC[rr++] = vv;
  rr = "a".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;
  rr = "A".charCodeAt(0);
  for (vv = 10; vv < 36; ++vv) BI_RC[rr++] = vv;

  function int2char(n) { return BI_RM.charAt(n); }
  function intAt(s, i) {
    var c = BI_RC[s.charCodeAt(i)];
    return (c == null) ? -1 : c;
  }

  // (protected) copy this to r
  function bnpCopyTo(r) {
    for (var i = this.t - 1; i >= 0; --i) r[i] = this[i];
    r.t = this.t;
    r.s = this.s;
  }

  // (protected) set from integer value x, -DV <= x < DV
  function bnpFromInt(x) {
    this.t = 1;
    this.s = (x < 0) ? -1 : 0;
    if (x > 0) this[0] = x;
    else if (x < -1) this[0] = x + this.DV;
    else this.t = 0;
  }

  // return bigint initialized to value
  function nbv(i) { var r = nbi(); r.fromInt(i); return r; }

  // (protected) set from string and radix
  function bnpFromString(s, b) {
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 256) k = 8; // byte array
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else { this.fromRadix(s, b); return; }
    this.t = 0;
    this.s = 0;
    var i = s.length, mi = false, sh = 0;
    while (--i >= 0) {
      var x = (k == 8) ? s[i] & 0xff : intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-") mi = true;
        continue;
      }
      mi = false;
      if (sh == 0)
        this[this.t++] = x;
      else if (sh + k > this.DB) {
        this[this.t - 1] |= (x & ((1 << (this.DB - sh)) - 1)) << sh;
        this[this.t++] = (x >> (this.DB - sh));
      }
      else
        this[this.t - 1] |= x << sh;
      sh += k;
      if (sh >= this.DB) sh -= this.DB;
    }
    if (k == 8 && (s[0] & 0x80) != 0) {
      this.s = -1;
      if (sh > 0) this[this.t - 1] |= ((1 << (this.DB - sh)) - 1) << sh;
    }
    this.clamp();
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) clamp off excess high words
  function bnpClamp() {
    var c = this.s & this.DM;
    while (this.t > 0 && this[this.t - 1] == c)--this.t;
  }

  // (public) return string representation in given radix
  function bnToString(b) {
    if (this.s < 0) return "-" + this.negate().toString(b);
    var k;
    if (b == 16) k = 4;
    else if (b == 8) k = 3;
    else if (b == 2) k = 1;
    else if (b == 32) k = 5;
    else if (b == 4) k = 2;
    else return this.toRadix(b);
    var km = (1 << k) - 1, d, m = false, r = "", i = this.t;
    var p = this.DB - (i * this.DB) % k;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) > 0) { m = true; r = int2char(d); }
      while (i >= 0) {
        if (p < k) {
          d = (this[i] & ((1 << p) - 1)) << (k - p);
          d |= this[--i] >> (p += this.DB - k);
        }
        else {
          d = (this[i] >> (p -= k)) & km;
          if (p <= 0) { p += this.DB; --i; }
        }
        if (d > 0) m = true;
        if (m) r += int2char(d);
      }
    }
    return m ? r : "0";
  }

  // (public) -this
  function bnNegate() { var r = nbi(); BigInteger.ZERO.subTo(this, r); return r; }

  // (public) |this|
  function bnAbs() { return (this.s < 0) ? this.negate() : this; }

  // (public) return + if this > a, - if this < a, 0 if equal
  function bnCompareTo(a) {
    var r = this.s - a.s;
    if (r != 0) return r;
    var i = this.t;
    r = i - a.t;
    if (r != 0) return (this.s < 0) ? -r : r;
    while (--i >= 0) if ((r = this[i] - a[i]) != 0) return r;
    return 0;
  }

  // returns bit length of the integer x
  function nbits(x) {
    var r = 1, t;
    if ((t = x >>> 16) != 0) { x = t; r += 16; }
    if ((t = x >> 8) != 0) { x = t; r += 8; }
    if ((t = x >> 4) != 0) { x = t; r += 4; }
    if ((t = x >> 2) != 0) { x = t; r += 2; }
    if ((t = x >> 1) != 0) { x = t; r += 1; }
    return r;
  }

  // (public) return the number of bits in "this"
  function bnBitLength() {
    if (this.t <= 0) return 0;
    return this.DB * (this.t - 1) + nbits(this[this.t - 1] ^ (this.s & this.DM));
  }

  // (protected) r = this << n*DB
  function bnpDLShiftTo(n, r) {
    var i;
    for (i = this.t - 1; i >= 0; --i) r[i + n] = this[i];
    for (i = n - 1; i >= 0; --i) r[i] = 0;
    r.t = this.t + n;
    r.s = this.s;
  }

  // (protected) r = this >> n*DB
  function bnpDRShiftTo(n, r) {
    for (var i = n; i < this.t; ++i) r[i - n] = this[i];
    r.t = Math.max(this.t - n, 0);
    r.s = this.s;
  }

  // (protected) r = this << n
  function bnpLShiftTo(n, r) {
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << cbs) - 1;
    var ds = Math.floor(n / this.DB), c = (this.s << bs) & this.DM, i;
    for (i = this.t - 1; i >= 0; --i) {
      r[i + ds + 1] = (this[i] >> cbs) | c;
      c = (this[i] & bm) << bs;
    }
    for (i = ds - 1; i >= 0; --i) r[i] = 0;
    r[ds] = c;
    r.t = this.t + ds + 1;
    r.s = this.s;
    r.clamp();
  }

  // (protected) r = this >> n
  function bnpRShiftTo(n, r) {
    r.s = this.s;
    var ds = Math.floor(n / this.DB);
    if (ds >= this.t) { r.t = 0; return; }
    var bs = n % this.DB;
    var cbs = this.DB - bs;
    var bm = (1 << bs) - 1;
    r[0] = this[ds] >> bs;
    for (var i = ds + 1; i < this.t; ++i) {
      r[i - ds - 1] |= (this[i] & bm) << cbs;
      r[i - ds] = this[i] >> bs;
    }
    if (bs > 0) r[this.t - ds - 1] |= (this.s & bm) << cbs;
    r.t = this.t - ds;
    r.clamp();
  }

  // (protected) r = this - a
  function bnpSubTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] - a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c -= a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c -= a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c -= a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c < -1) r[i++] = this.DV + c;
    else if (c > 0) r[i++] = c;
    r.t = i;
    r.clamp();
  }

  // (protected) r = this * a, r != this,a (HAC 14.12)
  // "this" should be the larger one if appropriate.
  function bnpMultiplyTo(a, r) {
    var x = this.abs(), y = a.abs();
    var i = x.t;
    r.t = i + y.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < y.t; ++i) r[i + x.t] = x.am(0, y[i], r, i, 0, x.t);
    r.s = 0;
    r.clamp();
    if (this.s != a.s) BigInteger.ZERO.subTo(r, r);
  }

  // (protected) r = this^2, r != this (HAC 14.16)
  function bnpSquareTo(r) {
    var x = this.abs();
    var i = r.t = 2 * x.t;
    while (--i >= 0) r[i] = 0;
    for (i = 0; i < x.t - 1; ++i) {
      var c = x.am(i, x[i], r, 2 * i, 0, 1);
      if ((r[i + x.t] += x.am(i + 1, 2 * x[i], r, 2 * i + 1, c, x.t - i - 1)) >= x.DV) {
        r[i + x.t] -= x.DV;
        r[i + x.t + 1] = 1;
      }
    }
    if (r.t > 0) r[r.t - 1] += x.am(i, x[i], r, 2 * i, 0, 1);
    r.s = 0;
    r.clamp();
  }

  // (protected) divide this by m, quotient and remainder to q, r (HAC 14.20)
  // r != q, this != m.  q or r may be null.
  function bnpDivRemTo(m, q, r) {
    var pm = m.abs();
    if (pm.t <= 0) return;
    var pt = this.abs();
    if (pt.t < pm.t) {
      if (q != null) q.fromInt(0);
      if (r != null) this.copyTo(r);
      return;
    }
    if (r == null) r = nbi();
    var y = nbi(), ts = this.s, ms = m.s;
    var nsh = this.DB - nbits(pm[pm.t - 1]);   // normalize modulus
    if (nsh > 0) { pm.lShiftTo(nsh, y); pt.lShiftTo(nsh, r); }
    else { pm.copyTo(y); pt.copyTo(r); }
    var ys = y.t;
    var y0 = y[ys - 1];
    if (y0 == 0) return;
    var yt = y0 * (1 << this.F1) + ((ys > 1) ? y[ys - 2] >> this.F2 : 0);
    var d1 = this.FV / yt, d2 = (1 << this.F1) / yt, e = 1 << this.F2;
    var i = r.t, j = i - ys, t = (q == null) ? nbi() : q;
    y.dlShiftTo(j, t);
    if (r.compareTo(t) >= 0) {
      r[r.t++] = 1;
      r.subTo(t, r);
    }
    BigInteger.ONE.dlShiftTo(ys, t);
    t.subTo(y, y);  // "negative" y so we can replace sub with am later
    while (y.t < ys) y[y.t++] = 0;
    while (--j >= 0) {
      // Estimate quotient digit
      var qd = (r[--i] == y0) ? this.DM : Math.floor(r[i] * d1 + (r[i - 1] + e) * d2);
      if ((r[i] += y.am(0, qd, r, j, 0, ys)) < qd) {   // Try it out
        y.dlShiftTo(j, t);
        r.subTo(t, r);
        while (r[i] < --qd) r.subTo(t, r);
      }
    }
    if (q != null) {
      r.drShiftTo(ys, q);
      if (ts != ms) BigInteger.ZERO.subTo(q, q);
    }
    r.t = ys;
    r.clamp();
    if (nsh > 0) r.rShiftTo(nsh, r); // Denormalize remainder
    if (ts < 0) BigInteger.ZERO.subTo(r, r);
  }

  // (public) this mod a
  function bnMod(a) {
    var r = nbi();
    this.abs().divRemTo(a, null, r);
    if (this.s < 0 && r.compareTo(BigInteger.ZERO) > 0) a.subTo(r, r);
    return r;
  }

  // Modular reduction using "classic" algorithm
  function Classic(m) { this.m = m; }
  function cConvert(x) {
    if (x.s < 0 || x.compareTo(this.m) >= 0) return x.mod(this.m);
    else return x;
  }
  function cRevert(x) { return x; }
  function cReduce(x) { x.divRemTo(this.m, null, x); }
  function cMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }
  function cSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  Classic.prototype.convert = cConvert;
  Classic.prototype.revert = cRevert;
  Classic.prototype.reduce = cReduce;
  Classic.prototype.mulTo = cMulTo;
  Classic.prototype.sqrTo = cSqrTo;

  // (protected) return "-1/this % 2^DB"; useful for Mont. reduction
  // justification:
  //         xy == 1 (mod m)
  //         xy =  1+km
  //   xy(2-xy) = (1+km)(1-km)
  // x[y(2-xy)] = 1-k^2m^2
  // x[y(2-xy)] == 1 (mod m^2)
  // if y is 1/x mod m, then y(2-xy) is 1/x mod m^2
  // should reduce x and y(2-xy) by m^2 at each step to keep size bounded.
  // JS multiply "overflows" differently from C/C++, so care is needed here.
  function bnpInvDigit() {
    if (this.t < 1) return 0;
    var x = this[0];
    if ((x & 1) == 0) return 0;
    var y = x & 3;       // y == 1/x mod 2^2
    y = (y * (2 - (x & 0xf) * y)) & 0xf; // y == 1/x mod 2^4
    y = (y * (2 - (x & 0xff) * y)) & 0xff;   // y == 1/x mod 2^8
    y = (y * (2 - (((x & 0xffff) * y) & 0xffff))) & 0xffff;    // y == 1/x mod 2^16
    // last step - calculate inverse mod DV directly;
    // assumes 16 < DB <= 32 and assumes ability to handle 48-bit ints
    y = (y * (2 - x * y % this.DV)) % this.DV;       // y == 1/x mod 2^dbits
    // we really want the negative inverse, and -DV < y < DV
    return (y > 0) ? this.DV - y : -y;
  }

  // Montgomery reduction
  function Montgomery(m) {
    this.m = m;
    this.mp = m.invDigit();
    this.mpl = this.mp & 0x7fff;
    this.mph = this.mp >> 15;
    this.um = (1 << (m.DB - 15)) - 1;
    this.mt2 = 2 * m.t;
  }

  // xR mod m
  function montConvert(x) {
    var r = nbi();
    x.abs().dlShiftTo(this.m.t, r);
    r.divRemTo(this.m, null, r);
    if (x.s < 0 && r.compareTo(BigInteger.ZERO) > 0) this.m.subTo(r, r);
    return r;
  }

  // x/R mod m
  function montRevert(x) {
    var r = nbi();
    x.copyTo(r);
    this.reduce(r);
    return r;
  }

  // x = x/R mod m (HAC 14.32)
  function montReduce(x) {
    while (x.t <= this.mt2) // pad x so am has enough room later
      x[x.t++] = 0;
    for (var i = 0; i < this.m.t; ++i) {
      // faster way of calculating u0 = x[i]*mp mod DV
      var j = x[i] & 0x7fff;
      var u0 = (j * this.mpl + (((j * this.mph + (x[i] >> 15) * this.mpl) & this.um) << 15)) & x.DM;
      // use am to combine the multiply-shift-add into one call
      j = i + this.m.t;
      x[j] += this.m.am(0, u0, x, i, 0, this.m.t);
      // propagate carry
      while (x[j] >= x.DV) { x[j] -= x.DV; x[++j]++; }
    }
    x.clamp();
    x.drShiftTo(this.m.t, x);
    if (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = "x^2/R mod m"; x != r
  function montSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = "xy/R mod m"; x,y != r
  function montMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Montgomery.prototype.convert = montConvert;
  Montgomery.prototype.revert = montRevert;
  Montgomery.prototype.reduce = montReduce;
  Montgomery.prototype.mulTo = montMulTo;
  Montgomery.prototype.sqrTo = montSqrTo;

  // (protected) true iff this is even
  function bnpIsEven() { return ((this.t > 0) ? (this[0] & 1) : this.s) == 0; }

  // (protected) this^e, e < 2^32, doing sqr and mul with "r" (HAC 14.79)
  function bnpExp(e, z) {
    if (e > 0xffffffff || e < 1) return BigInteger.ONE;
    var r = nbi(), r2 = nbi(), g = z.convert(this), i = nbits(e) - 1;
    g.copyTo(r);
    while (--i >= 0) {
      z.sqrTo(r, r2);
      if ((e & (1 << i)) > 0) z.mulTo(r2, g, r);
      else { var t = r; r = r2; r2 = t; }
    }
    return z.revert(r);
  }

  // (public) this^e % m, 0 <= e < 2^32
  function bnModPowInt(e, m) {
    var z;
    if (e < 256 || m.isEven()) z = new Classic(m); else z = new Montgomery(m);
    return this.exp(e, z);
  }

  // protected
  BigInteger.prototype.copyTo = bnpCopyTo;
  BigInteger.prototype.fromInt = bnpFromInt;
  BigInteger.prototype.fromString = bnpFromString;
  BigInteger.prototype.clamp = bnpClamp;
  BigInteger.prototype.dlShiftTo = bnpDLShiftTo;
  BigInteger.prototype.drShiftTo = bnpDRShiftTo;
  BigInteger.prototype.lShiftTo = bnpLShiftTo;
  BigInteger.prototype.rShiftTo = bnpRShiftTo;
  BigInteger.prototype.subTo = bnpSubTo;
  BigInteger.prototype.multiplyTo = bnpMultiplyTo;
  BigInteger.prototype.squareTo = bnpSquareTo;
  BigInteger.prototype.divRemTo = bnpDivRemTo;
  BigInteger.prototype.invDigit = bnpInvDigit;
  BigInteger.prototype.isEven = bnpIsEven;
  BigInteger.prototype.exp = bnpExp;

  // public
  BigInteger.prototype.toString = bnToString;
  BigInteger.prototype.negate = bnNegate;
  BigInteger.prototype.abs = bnAbs;
  BigInteger.prototype.compareTo = bnCompareTo;
  BigInteger.prototype.bitLength = bnBitLength;
  BigInteger.prototype.mod = bnMod;
  BigInteger.prototype.modPowInt = bnModPowInt;

  // "constants"
  BigInteger.ZERO = nbv(0);
  BigInteger.ONE = nbv(1);

  // Copyright (c) 2005-2009  Tom Wu
  // All Rights Reserved.
  // See "LICENSE" for details.

  // Extended JavaScript BN functions, required for RSA private ops.

  // Version 1.1: new BigInteger("0", 10) returns "proper" zero
  // Version 1.2: square() API, isProbablePrime fix

  // (public)
  function bnClone() { var r = nbi(); this.copyTo(r); return r; }

  // (public) return value as integer
  function bnIntValue() {
    if (this.s < 0) {
      if (this.t == 1) return this[0] - this.DV;
      else if (this.t == 0) return -1;
    }
    else if (this.t == 1) return this[0];
    else if (this.t == 0) return 0;
    // assumes 16 < DB < 32
    return ((this[1] & ((1 << (32 - this.DB)) - 1)) << this.DB) | this[0];
  }

  // (public) return value as byte
  function bnByteValue() { return (this.t == 0) ? this.s : (this[0] << 24) >> 24; }

  // (public) return value as short (assumes DB>=16)
  function bnShortValue() { return (this.t == 0) ? this.s : (this[0] << 16) >> 16; }

  // (protected) return x s.t. r^x < DV
  function bnpChunkSize(r) { return Math.floor(Math.LN2 * this.DB / Math.log(r)); }

  // (public) 0 if this == 0, 1 if this > 0
  function bnSigNum() {
    if (this.s < 0) return -1;
    else if (this.t <= 0 || (this.t == 1 && this[0] <= 0)) return 0;
    else return 1;
  }

  // (protected) convert to radix string
  function bnpToRadix(b) {
    if (b == null) b = 10;
    if (this.signum() == 0 || b < 2 || b > 36) return "0";
    var cs = this.chunkSize(b);
    var a = Math.pow(b, cs);
    var d = nbv(a), y = nbi(), z = nbi(), r = "";
    this.divRemTo(d, y, z);
    while (y.signum() > 0) {
      r = (a + z.intValue()).toString(b).substr(1) + r;
      y.divRemTo(d, y, z);
    }
    return z.intValue().toString(b) + r;
  }

  // (protected) convert from radix string
  function bnpFromRadix(s, b) {
    this.fromInt(0);
    if (b == null) b = 10;
    var cs = this.chunkSize(b);
    var d = Math.pow(b, cs), mi = false, j = 0, w = 0;
    for (var i = 0; i < s.length; ++i) {
      var x = intAt(s, i);
      if (x < 0) {
        if (s.charAt(i) == "-" && this.signum() == 0) mi = true;
        continue;
      }
      w = b * w + x;
      if (++j >= cs) {
        this.dMultiply(d);
        this.dAddOffset(w, 0);
        j = 0;
        w = 0;
      }
    }
    if (j > 0) {
      this.dMultiply(Math.pow(b, j));
      this.dAddOffset(w, 0);
    }
    if (mi) BigInteger.ZERO.subTo(this, this);
  }

  // (protected) alternate constructor
  function bnpFromNumber(a, b, c) {
    if ("number" == typeof b) {
      // new BigInteger(int,int,RNG)
      if (a < 2) this.fromInt(1);
      else {
        this.fromNumber(a, c);
        if (!this.testBit(a - 1))    // force MSB set
          this.bitwiseTo(BigInteger.ONE.shiftLeft(a - 1), op_or, this);
        if (this.isEven()) this.dAddOffset(1, 0); // force odd
        while (!this.isProbablePrime(b)) {
          this.dAddOffset(2, 0);
          if (this.bitLength() > a) this.subTo(BigInteger.ONE.shiftLeft(a - 1), this);
        }
      }
    }
    else {
      // new BigInteger(int,RNG)
      var x = new Array(), t = a & 7;
      x.length = (a >> 3) + 1;
      b.nextBytes(x);
      if (t > 0) x[0] &= ((1 << t) - 1); else x[0] = 0;
      this.fromString(x, 256);
    }
  }

  // (public) convert to bigendian byte array
  function bnToByteArray() {
    var i = this.t, r = new Array();
    r[0] = this.s;
    var p = this.DB - (i * this.DB) % 8, d, k = 0;
    if (i-- > 0) {
      if (p < this.DB && (d = this[i] >> p) != (this.s & this.DM) >> p)
        r[k++] = d | (this.s << (this.DB - p));
      while (i >= 0) {
        if (p < 8) {
          d = (this[i] & ((1 << p) - 1)) << (8 - p);
          d |= this[--i] >> (p += this.DB - 8);
        }
        else {
          d = (this[i] >> (p -= 8)) & 0xff;
          if (p <= 0) { p += this.DB; --i; }
        }
        if ((d & 0x80) != 0) d |= -256;
        if (k == 0 && (this.s & 0x80) != (d & 0x80))++k;
        if (k > 0 || d != this.s) r[k++] = d;
      }
    }
    return r;
  }

  function bnEquals(a) { return (this.compareTo(a) == 0); }
  function bnMin(a) { return (this.compareTo(a) < 0) ? this : a; }
  function bnMax(a) { return (this.compareTo(a) > 0) ? this : a; }

  // (protected) r = this op a (bitwise)
  function bnpBitwiseTo(a, op, r) {
    var i, f, m = Math.min(a.t, this.t);
    for (i = 0; i < m; ++i) r[i] = op(this[i], a[i]);
    if (a.t < this.t) {
      f = a.s & this.DM;
      for (i = m; i < this.t; ++i) r[i] = op(this[i], f);
      r.t = this.t;
    }
    else {
      f = this.s & this.DM;
      for (i = m; i < a.t; ++i) r[i] = op(f, a[i]);
      r.t = a.t;
    }
    r.s = op(this.s, a.s);
    r.clamp();
  }

  // (public) this & a
  function op_and(x, y) { return x & y; }
  function bnAnd(a) { var r = nbi(); this.bitwiseTo(a, op_and, r); return r; }

  // (public) this | a
  function op_or(x, y) { return x | y; }
  function bnOr(a) { var r = nbi(); this.bitwiseTo(a, op_or, r); return r; }

  // (public) this ^ a
  function op_xor(x, y) { return x ^ y; }
  function bnXor(a) { var r = nbi(); this.bitwiseTo(a, op_xor, r); return r; }

  // (public) this & ~a
  function op_andnot(x, y) { return x & ~y; }
  function bnAndNot(a) { var r = nbi(); this.bitwiseTo(a, op_andnot, r); return r; }

  // (public) ~this
  function bnNot() {
    var r = nbi();
    for (var i = 0; i < this.t; ++i) r[i] = this.DM & ~this[i];
    r.t = this.t;
    r.s = ~this.s;
    return r;
  }

  // (public) this << n
  function bnShiftLeft(n) {
    var r = nbi();
    if (n < 0) this.rShiftTo(-n, r); else this.lShiftTo(n, r);
    return r;
  }

  // (public) this >> n
  function bnShiftRight(n) {
    var r = nbi();
    if (n < 0) this.lShiftTo(-n, r); else this.rShiftTo(n, r);
    return r;
  }

  // return index of lowest 1-bit in x, x < 2^31
  function lbit(x) {
    if (x == 0) return -1;
    var r = 0;
    if ((x & 0xffff) == 0) { x >>= 16; r += 16; }
    if ((x & 0xff) == 0) { x >>= 8; r += 8; }
    if ((x & 0xf) == 0) { x >>= 4; r += 4; }
    if ((x & 3) == 0) { x >>= 2; r += 2; }
    if ((x & 1) == 0)++r;
    return r;
  }

  // (public) returns index of lowest 1-bit (or -1 if none)
  function bnGetLowestSetBit() {
    for (var i = 0; i < this.t; ++i)
      if (this[i] != 0) return i * this.DB + lbit(this[i]);
    if (this.s < 0) return this.t * this.DB;
    return -1;
  }

  // return number of 1 bits in x
  function cbit(x) {
    var r = 0;
    while (x != 0) { x &= x - 1; ++r; }
    return r;
  }

  // (public) return number of set bits
  function bnBitCount() {
    var r = 0, x = this.s & this.DM;
    for (var i = 0; i < this.t; ++i) r += cbit(this[i] ^ x);
    return r;
  }

  // (public) true iff nth bit is set
  function bnTestBit(n) {
    var j = Math.floor(n / this.DB);
    if (j >= this.t) return (this.s != 0);
    return ((this[j] & (1 << (n % this.DB))) != 0);
  }

  // (protected) this op (1<<n)
  function bnpChangeBit(n, op) {
    var r = BigInteger.ONE.shiftLeft(n);
    this.bitwiseTo(r, op, r);
    return r;
  }

  // (public) this | (1<<n)
  function bnSetBit(n) { return this.changeBit(n, op_or); }

  // (public) this & ~(1<<n)
  function bnClearBit(n) { return this.changeBit(n, op_andnot); }

  // (public) this ^ (1<<n)
  function bnFlipBit(n) { return this.changeBit(n, op_xor); }

  // (protected) r = this + a
  function bnpAddTo(a, r) {
    var i = 0, c = 0, m = Math.min(a.t, this.t);
    while (i < m) {
      c += this[i] + a[i];
      r[i++] = c & this.DM;
      c >>= this.DB;
    }
    if (a.t < this.t) {
      c += a.s;
      while (i < this.t) {
        c += this[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += this.s;
    }
    else {
      c += this.s;
      while (i < a.t) {
        c += a[i];
        r[i++] = c & this.DM;
        c >>= this.DB;
      }
      c += a.s;
    }
    r.s = (c < 0) ? -1 : 0;
    if (c > 0) r[i++] = c;
    else if (c < -1) r[i++] = this.DV + c;
    r.t = i;
    r.clamp();
  }

  // (public) this + a
  function bnAdd(a) { var r = nbi(); this.addTo(a, r); return r; }

  // (public) this - a
  function bnSubtract(a) { var r = nbi(); this.subTo(a, r); return r; }

  // (public) this * a
  function bnMultiply(a) { var r = nbi(); this.multiplyTo(a, r); return r; }

  // (public) this^2
  function bnSquare() { var r = nbi(); this.squareTo(r); return r; }

  // (public) this / a
  function bnDivide(a) { var r = nbi(); this.divRemTo(a, r, null); return r; }

  // (public) this % a
  function bnRemainder(a) { var r = nbi(); this.divRemTo(a, null, r); return r; }

  // (public) [this/a,this%a]
  function bnDivideAndRemainder(a) {
    var q = nbi(), r = nbi();
    this.divRemTo(a, q, r);
    return new Array(q, r);
  }

  // (protected) this *= n, this >= 0, 1 < n < DV
  function bnpDMultiply(n) {
    this[this.t] = this.am(0, n - 1, this, 0, 0, this.t);
    ++this.t;
    this.clamp();
  }

  // (protected) this += n << w words, this >= 0
  function bnpDAddOffset(n, w) {
    if (n == 0) return;
    while (this.t <= w) this[this.t++] = 0;
    this[w] += n;
    while (this[w] >= this.DV) {
      this[w] -= this.DV;
      if (++w >= this.t) this[this.t++] = 0;
      ++this[w];
    }
  }

  // A "null" reducer
  function NullExp() { }
  function nNop(x) { return x; }
  function nMulTo(x, y, r) { x.multiplyTo(y, r); }
  function nSqrTo(x, r) { x.squareTo(r); }

  NullExp.prototype.convert = nNop;
  NullExp.prototype.revert = nNop;
  NullExp.prototype.mulTo = nMulTo;
  NullExp.prototype.sqrTo = nSqrTo;

  // (public) this^e
  function bnPow(e) { return this.exp(e, new NullExp()); }

  // (protected) r = lower n words of "this * a", a.t <= n
  // "this" should be the larger one if appropriate.
  function bnpMultiplyLowerTo(a, n, r) {
    var i = Math.min(this.t + a.t, n);
    r.s = 0; // assumes a,this >= 0
    r.t = i;
    while (i > 0) r[--i] = 0;
    var j;
    for (j = r.t - this.t; i < j; ++i) r[i + this.t] = this.am(0, a[i], r, i, 0, this.t);
    for (j = Math.min(a.t, n); i < j; ++i) this.am(0, a[i], r, i, 0, n - i);
    r.clamp();
  }

  // (protected) r = "this * a" without lower n words, n > 0
  // "this" should be the larger one if appropriate.
  function bnpMultiplyUpperTo(a, n, r) {
    --n;
    var i = r.t = this.t + a.t - n;
    r.s = 0; // assumes a,this >= 0
    while (--i >= 0) r[i] = 0;
    for (i = Math.max(n - this.t, 0); i < a.t; ++i)
      r[this.t + i - n] = this.am(n - i, a[i], r, 0, 0, this.t + i - n);
    r.clamp();
    r.drShiftTo(1, r);
  }

  // Barrett modular reduction
  function Barrett(m) {
    // setup Barrett
    this.r2 = nbi();
    this.q3 = nbi();
    BigInteger.ONE.dlShiftTo(2 * m.t, this.r2);
    this.mu = this.r2.divide(m);
    this.m = m;
  }

  function barrettConvert(x) {
    if (x.s < 0 || x.t > 2 * this.m.t) return x.mod(this.m);
    else if (x.compareTo(this.m) < 0) return x;
    else { var r = nbi(); x.copyTo(r); this.reduce(r); return r; }
  }

  function barrettRevert(x) { return x; }

  // x = x mod m (HAC 14.42)
  function barrettReduce(x) {
    x.drShiftTo(this.m.t - 1, this.r2);
    if (x.t > this.m.t + 1) { x.t = this.m.t + 1; x.clamp(); }
    this.mu.multiplyUpperTo(this.r2, this.m.t + 1, this.q3);
    this.m.multiplyLowerTo(this.q3, this.m.t + 1, this.r2);
    while (x.compareTo(this.r2) < 0) x.dAddOffset(1, this.m.t + 1);
    x.subTo(this.r2, x);
    while (x.compareTo(this.m) >= 0) x.subTo(this.m, x);
  }

  // r = x^2 mod m; x != r
  function barrettSqrTo(x, r) { x.squareTo(r); this.reduce(r); }

  // r = x*y mod m; x,y != r
  function barrettMulTo(x, y, r) { x.multiplyTo(y, r); this.reduce(r); }

  Barrett.prototype.convert = barrettConvert;
  Barrett.prototype.revert = barrettRevert;
  Barrett.prototype.reduce = barrettReduce;
  Barrett.prototype.mulTo = barrettMulTo;
  Barrett.prototype.sqrTo = barrettSqrTo;

  // (public) this^e % m (HAC 14.85)
  function bnModPow(e, m) {
    var i = e.bitLength(), k, r = nbv(1), z;
    if (i <= 0) return r;
    else if (i < 18) k = 1;
    else if (i < 48) k = 3;
    else if (i < 144) k = 4;
    else if (i < 768) k = 5;
    else k = 6;
    if (i < 8)
      z = new Classic(m);
    else if (m.isEven())
      z = new Barrett(m);
    else
      z = new Montgomery(m);

    // precomputation
    var g = new Array(), n = 3, k1 = k - 1, km = (1 << k) - 1;
    g[1] = z.convert(this);
    if (k > 1) {
      var g2 = nbi();
      z.sqrTo(g[1], g2);
      while (n <= km) {
        g[n] = nbi();
        z.mulTo(g2, g[n - 2], g[n]);
        n += 2;
      }
    }

    var j = e.t - 1, w, is1 = true, r2 = nbi(), t;
    i = nbits(e[j]) - 1;
    while (j >= 0) {
      if (i >= k1) w = (e[j] >> (i - k1)) & km;
      else {
        w = (e[j] & ((1 << (i + 1)) - 1)) << (k1 - i);
        if (j > 0) w |= e[j - 1] >> (this.DB + i - k1);
      }

      n = k;
      while ((w & 1) == 0) { w >>= 1; --n; }
      if ((i -= n) < 0) { i += this.DB; --j; }
      if (is1) {    // ret == 1, don't bother squaring or multiplying it
        g[w].copyTo(r);
        is1 = false;
      }
      else {
        while (n > 1) { z.sqrTo(r, r2); z.sqrTo(r2, r); n -= 2; }
        if (n > 0) z.sqrTo(r, r2); else { t = r; r = r2; r2 = t; }
        z.mulTo(r2, g[w], r);
      }

      while (j >= 0 && (e[j] & (1 << i)) == 0) {
        z.sqrTo(r, r2); t = r; r = r2; r2 = t;
        if (--i < 0) { i = this.DB - 1; --j; }
      }
    }
    return z.revert(r);
  }

  // (public) gcd(this,a) (HAC 14.54)
  function bnGCD(a) {
    var x = (this.s < 0) ? this.negate() : this.clone();
    var y = (a.s < 0) ? a.negate() : a.clone();
    if (x.compareTo(y) < 0) { var t = x; x = y; y = t; }
    var i = x.getLowestSetBit(), g = y.getLowestSetBit();
    if (g < 0) return x;
    if (i < g) g = i;
    if (g > 0) {
      x.rShiftTo(g, x);
      y.rShiftTo(g, y);
    }
    while (x.signum() > 0) {
      if ((i = x.getLowestSetBit()) > 0) x.rShiftTo(i, x);
      if ((i = y.getLowestSetBit()) > 0) y.rShiftTo(i, y);
      if (x.compareTo(y) >= 0) {
        x.subTo(y, x);
        x.rShiftTo(1, x);
      }
      else {
        y.subTo(x, y);
        y.rShiftTo(1, y);
      }
    }
    if (g > 0) y.lShiftTo(g, y);
    return y;
  }

  // (protected) this % n, n < 2^26
  function bnpModInt(n) {
    if (n <= 0) return 0;
    var d = this.DV % n, r = (this.s < 0) ? n - 1 : 0;
    if (this.t > 0)
      if (d == 0) r = this[0] % n;
      else for (var i = this.t - 1; i >= 0; --i) r = (d * r + this[i]) % n;
    return r;
  }

  // (public) 1/this % m (HAC 14.61)
  function bnModInverse(m) {
    var ac = m.isEven();
    if ((this.isEven() && ac) || m.signum() == 0) return BigInteger.ZERO;
    var u = m.clone(), v = this.clone();
    var a = nbv(1), b = nbv(0), c = nbv(0), d = nbv(1);
    while (u.signum() != 0) {
      while (u.isEven()) {
        u.rShiftTo(1, u);
        if (ac) {
          if (!a.isEven() || !b.isEven()) { a.addTo(this, a); b.subTo(m, b); }
          a.rShiftTo(1, a);
        }
        else if (!b.isEven()) b.subTo(m, b);
        b.rShiftTo(1, b);
      }
      while (v.isEven()) {
        v.rShiftTo(1, v);
        if (ac) {
          if (!c.isEven() || !d.isEven()) { c.addTo(this, c); d.subTo(m, d); }
          c.rShiftTo(1, c);
        }
        else if (!d.isEven()) d.subTo(m, d);
        d.rShiftTo(1, d);
      }
      if (u.compareTo(v) >= 0) {
        u.subTo(v, u);
        if (ac) a.subTo(c, a);
        b.subTo(d, b);
      }
      else {
        v.subTo(u, v);
        if (ac) c.subTo(a, c);
        d.subTo(b, d);
      }
    }
    if (v.compareTo(BigInteger.ONE) != 0) return BigInteger.ZERO;
    if (d.compareTo(m) >= 0) return d.subtract(m);
    if (d.signum() < 0) d.addTo(m, d); else return d;
    if (d.signum() < 0) return d.add(m); else return d;
  }

  var lowprimes = [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37, 41, 43, 47, 53, 59, 61, 67, 71, 73, 79, 83, 89, 97, 101, 103, 107, 109, 113, 127, 131, 137, 139, 149, 151, 157, 163, 167, 173, 179, 181, 191, 193, 197, 199, 211, 223, 227, 229, 233, 239, 241, 251, 257, 263, 269, 271, 277, 281, 283, 293, 307, 311, 313, 317, 331, 337, 347, 349, 353, 359, 367, 373, 379, 383, 389, 397, 401, 409, 419, 421, 431, 433, 439, 443, 449, 457, 461, 463, 467, 479, 487, 491, 499, 503, 509, 521, 523, 541, 547, 557, 563, 569, 571, 577, 587, 593, 599, 601, 607, 613, 617, 619, 631, 641, 643, 647, 653, 659, 661, 673, 677, 683, 691, 701, 709, 719, 727, 733, 739, 743, 751, 757, 761, 769, 773, 787, 797, 809, 811, 821, 823, 827, 829, 839, 853, 857, 859, 863, 877, 881, 883, 887, 907, 911, 919, 929, 937, 941, 947, 953, 967, 971, 977, 983, 991, 997];
  var lplim = (1 << 26) / lowprimes[lowprimes.length - 1];

  // (public) test primality with certainty >= 1-.5^t
  function bnIsProbablePrime(t) {
    var i, x = this.abs();
    if (x.t == 1 && x[0] <= lowprimes[lowprimes.length - 1]) {
      for (i = 0; i < lowprimes.length; ++i)
        if (x[0] == lowprimes[i]) return true;
      return false;
    }
    if (x.isEven()) return false;
    i = 1;
    while (i < lowprimes.length) {
      var m = lowprimes[i], j = i + 1;
      while (j < lowprimes.length && m < lplim) m *= lowprimes[j++];
      m = x.modInt(m);
      while (i < j) if (m % lowprimes[i++] == 0) return false;
    }
    return x.millerRabin(t);
  }

  // (protected) true if probably prime (HAC 4.24, Miller-Rabin)
  function bnpMillerRabin(t) {
    var n1 = this.subtract(BigInteger.ONE);
    var k = n1.getLowestSetBit();
    if (k <= 0) return false;
    var r = n1.shiftRight(k);
    t = (t + 1) >> 1;
    if (t > lowprimes.length) t = lowprimes.length;
    var a = nbi();
    for (var i = 0; i < t; ++i) {
      //Pick bases at random, instead of starting at 2
      a.fromInt(lowprimes[Math.floor(Math.random() * lowprimes.length)]);
      var y = a.modPow(r, this);
      if (y.compareTo(BigInteger.ONE) != 0 && y.compareTo(n1) != 0) {
        var j = 1;
        while (j++ < k && y.compareTo(n1) != 0) {
          y = y.modPowInt(2, this);
          if (y.compareTo(BigInteger.ONE) == 0) return false;
        }
        if (y.compareTo(n1) != 0) return false;
      }
    }
    return true;
  }

  // protected
  BigInteger.prototype.chunkSize = bnpChunkSize;
  BigInteger.prototype.toRadix = bnpToRadix;
  BigInteger.prototype.fromRadix = bnpFromRadix;
  BigInteger.prototype.fromNumber = bnpFromNumber;
  BigInteger.prototype.bitwiseTo = bnpBitwiseTo;
  BigInteger.prototype.changeBit = bnpChangeBit;
  BigInteger.prototype.addTo = bnpAddTo;
  BigInteger.prototype.dMultiply = bnpDMultiply;
  BigInteger.prototype.dAddOffset = bnpDAddOffset;
  BigInteger.prototype.multiplyLowerTo = bnpMultiplyLowerTo;
  BigInteger.prototype.multiplyUpperTo = bnpMultiplyUpperTo;
  BigInteger.prototype.modInt = bnpModInt;
  BigInteger.prototype.millerRabin = bnpMillerRabin;

  // public
  BigInteger.prototype.clone = bnClone;
  BigInteger.prototype.intValue = bnIntValue;
  BigInteger.prototype.byteValue = bnByteValue;
  BigInteger.prototype.shortValue = bnShortValue;
  BigInteger.prototype.signum = bnSigNum;
  BigInteger.prototype.toByteArray = bnToByteArray;
  BigInteger.prototype.equals = bnEquals;
  BigInteger.prototype.min = bnMin;
  BigInteger.prototype.max = bnMax;
  BigInteger.prototype.and = bnAnd;
  BigInteger.prototype.or = bnOr;
  BigInteger.prototype.xor = bnXor;
  BigInteger.prototype.andNot = bnAndNot;
  BigInteger.prototype.not = bnNot;
  BigInteger.prototype.shiftLeft = bnShiftLeft;
  BigInteger.prototype.shiftRight = bnShiftRight;
  BigInteger.prototype.getLowestSetBit = bnGetLowestSetBit;
  BigInteger.prototype.bitCount = bnBitCount;
  BigInteger.prototype.testBit = bnTestBit;
  BigInteger.prototype.setBit = bnSetBit;
  BigInteger.prototype.clearBit = bnClearBit;
  BigInteger.prototype.flipBit = bnFlipBit;
  BigInteger.prototype.add = bnAdd;
  BigInteger.prototype.subtract = bnSubtract;
  BigInteger.prototype.multiply = bnMultiply;
  BigInteger.prototype.divide = bnDivide;
  BigInteger.prototype.remainder = bnRemainder;
  BigInteger.prototype.divideAndRemainder = bnDivideAndRemainder;
  BigInteger.prototype.modPow = bnModPow;
  BigInteger.prototype.modInverse = bnModInverse;
  BigInteger.prototype.pow = bnPow;
  BigInteger.prototype.gcd = bnGCD;
  BigInteger.prototype.isProbablePrime = bnIsProbablePrime;

  // JSBN-specific extension
  BigInteger.prototype.square = bnSquare;

  // Expose the Barrett function
  BigInteger.prototype.Barrett = Barrett

  // BigInteger interfaces not implemented in jsbn:

  // BigInteger(int signum, byte[] magnitude)
  // double doubleValue()
  // float floatValue()
  // int hashCode()
  // long longValue()
  // static BigInteger valueOf(long val)

  // Random number generator - requires a PRNG backend, e.g. prng4.js

  // For best results, put code like
  // <body onClick='rng_seed_time();' onKeyPress='rng_seed_time();'>
  // in your main HTML document.

  var rng_state;
  var rng_pool;
  var rng_pptr;

  // Mix in a 32-bit integer into the pool
  function rng_seed_int(x) {
    rng_pool[rng_pptr++] ^= x & 255;
    rng_pool[rng_pptr++] ^= (x >> 8) & 255;
    rng_pool[rng_pptr++] ^= (x >> 16) & 255;
    rng_pool[rng_pptr++] ^= (x >> 24) & 255;
    if (rng_pptr >= rng_psize) rng_pptr -= rng_psize;
  }

  // Mix in the current time (w/milliseconds) into the pool
  function rng_seed_time() {
    rng_seed_int(new Date().getTime());
  }

  // Initialize the pool with junk if needed.
  if (rng_pool == null) {
    rng_pool = new Array();
    rng_pptr = 0;
    var t;
    if (typeof window !== "undefined" && window.crypto) {
      if (window.crypto.getRandomValues) {
        // Use webcrypto if available
        var ua = new Uint8Array(32);
        window.crypto.getRandomValues(ua);
        for (t = 0; t < 32; ++t)
          rng_pool[rng_pptr++] = ua[t];
      }
      else if (navigator.appName == "Netscape" && navigator.appVersion < "5") {
        // Extract entropy (256 bits) from NS4 RNG if available
        var z = window.crypto.random(32);
        for (t = 0; t < z.length; ++t)
          rng_pool[rng_pptr++] = z.charCodeAt(t) & 255;
      }
    }
    while (rng_pptr < rng_psize) {  // extract some randomness from Math.random()
      t = Math.floor(65536 * Math.random());
      rng_pool[rng_pptr++] = t >>> 8;
      rng_pool[rng_pptr++] = t & 255;
    }
    rng_pptr = 0;
    rng_seed_time();
    //rng_seed_int(window.screenX);
    //rng_seed_int(window.screenY);
  }

  function rng_get_byte() {
    if (rng_state == null) {
      rng_seed_time();
      rng_state = prng_newstate();
      rng_state.init(rng_pool);
      for (rng_pptr = 0; rng_pptr < rng_pool.length; ++rng_pptr)
        rng_pool[rng_pptr] = 0;
      rng_pptr = 0;
      //rng_pool = null;
    }
    // TODO: allow reseeding after first request
    return rng_state.next();
  }

  function rng_get_bytes(ba) {
    var i;
    for (i = 0; i < ba.length; ++i) ba[i] = rng_get_byte();
  }

  function SecureRandom() { }

  SecureRandom.prototype.nextBytes = rng_get_bytes;

  // prng4.js - uses Arcfour as a PRNG

  function Arcfour() {
    this.i = 0;
    this.j = 0;
    this.S = new Array();
  }

  // Initialize arcfour context from key, an array of ints, each from [0..255]
  function ARC4init(key) {
    var i, j, t;
    for (i = 0; i < 256; ++i)
      this.S[i] = i;
    j = 0;
    for (i = 0; i < 256; ++i) {
      j = (j + this.S[i] + key[i % key.length]) & 255;
      t = this.S[i];
      this.S[i] = this.S[j];
      this.S[j] = t;
    }
    this.i = 0;
    this.j = 0;
  }

  function ARC4next() {
    var t;
    this.i = (this.i + 1) & 255;
    this.j = (this.j + this.S[this.i]) & 255;
    t = this.S[this.i];
    this.S[this.i] = this.S[this.j];
    this.S[this.j] = t;
    return this.S[(t + this.S[this.i]) & 255];
  }

  Arcfour.prototype.init = ARC4init;
  Arcfour.prototype.next = ARC4next;

  // Plug in your RNG constructor here
  function prng_newstate() {
    return new Arcfour();
  }

  // Pool size must be a multiple of 4 and greater than 32.
  // An array of bytes the size of the pool will be passed to init()
  var rng_psize = 256;

  return {
    BigInteger: BigInteger,
    SecureRandom: SecureRandom
  };

}).call(this);



function $partial_5_6$io_95_bind(x1, x2, x3, x4, x5){
    return (function(x6){
        return io_95_bind(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_0_1$prim_95__95_floatToStr(){
    return (function(x1){
        return prim_95__95_floatToStr(x1);
    });
}

function $partial_0_2$prim_95__95_strCons(){
    return (function(x1){
        return (function(x2){
            return prim_95__95_strCons(x1, x2);
        });
    });
}

function $partial_1_2$prim_95__95_strCons(x1){
    return (function(x2){
        return prim_95__95_strCons(x1, x2);
    });
}

function $partial_0_1$prim_95__95_toStrBigInt(){
    return (function(x1){
        return prim_95__95_toStrBigInt(x1);
    });
}

function $partial_0_1$prim_95__95_toStrInt(){
    return (function(x1){
        return prim_95__95_toStrInt(x1);
    });
}

function $partial_3_4$ParserCombinator___60__124__62_(x1, x2, x3){
    return (function(x4){
        return ParserCombinator___60__124__62_(x1, x2, x3, x4);
    });
}

function $partial_3_5$Environment__addBinding(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Environment__addBinding(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_0_1$Bools__and(){
    return (function(x1){
        return Bools__and(x1);
    });
}

function $partial_0_1$ParseNumber__binConverter(){
    return (function(x1){
        return ParseNumber__binConverter(x1);
    });
}

function $partial_3_4$Util__boolBinop(x1, x2, x3){
    return (function(x4){
        return Util__boolBinop(x1, x2, x3, x4);
    });
}

function $partial_0_1$Lists__car(){
    return (function(x1){
        return Lists__car(x1);
    });
}

function $partial_0_1$Lists__cdr(){
    return (function(x1){
        return Lists__cdr(x1);
    });
}

function $partial_0_1$Lists__cons(){
    return (function(x1){
        return Lists__cons(x1);
    });
}

function $partial_0_1$ParseNumber__decConverter(){
    return (function(x1){
        return ParseNumber__decConverter(x1);
    });
}

function $partial_0_1$Numbers__doSub(){
    return (function(x1){
        return Numbers__doSub(x1);
    });
}

function $partial_0_1$Lists__empty(){
    return (function(x1){
        return Lists__empty(x1);
    });
}

function $partial_0_1$Primitives__eqv(){
    return (function(x1){
        return Primitives__eqv(x1);
    });
}

function $partial_3_4$Eval__eval(x1, x2, x3){
    return (function(x4){
        return Eval__eval(x1, x2, x3, x4);
    });
}

function $partial_2_3$ParserCombinator__failure(x1, x2){
    return (function(x3){
        return ParserCombinator__failure(x1, x2, x3);
    });
}

function $partial_0_1$ParseNumber__hexConverter(){
    return (function(x1){
        return ParseNumber__hexConverter(x1);
    });
}

function $partial_4_5$Util__initEnv_39_(x1, x2, x3, x4){
    return (function(x5){
        return Util__initEnv_39_(x1, x2, x3, x4, x5);
    });
}

function $partial_4_5$Control__IOExcept__ioe_95_lift(x1, x2, x3, x4){
    return (function(x5){
        return Control__IOExcept__ioe_95_lift(x1, x2, x3, x4, x5);
    });
}

function $partial_7_8$Control__IOExcept__ioe_95_run(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Control__IOExcept__ioe_95_run(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_0_1$Bools__isBoolean(){
    return (function(x1){
        return Bools__isBoolean(x1);
    });
}

function $partial_0_1$Primitives__isChar(){
    return (function(x1){
        return Primitives__isChar(x1);
    });
}

function $partial_0_1$Prelude__Chars__isDigit(){
    return (function(x1){
        return Prelude__Chars__isDigit(x1);
    });
}

function $partial_0_1$Numbers__isInteger(){
    return (function(x1){
        return Numbers__isInteger(x1);
    });
}

function $partial_0_1$Lists__isList(){
    return (function(x1){
        return Lists__isList(x1);
    });
}

function $partial_0_1$Lists__isPair(){
    return (function(x1){
        return Lists__isPair(x1);
    });
}

function $partial_0_1$Procedures__isProcedure(){
    return (function(x1){
        return Procedures__isProcedure(x1);
    });
}

function $partial_0_1$Prelude__Chars__isSpace(){
    return (function(x1){
        return Prelude__Chars__isSpace(x1);
    });
}

function $partial_0_1$Strings__isString(){
    return (function(x1){
        return Strings__isString(x1);
    });
}

function $partial_0_1$Symbols__isSymbol(){
    return (function(x1){
        return Symbols__isSymbol(x1);
    });
}

function $partial_0_1$Vector__isVector(){
    return (function(x1){
        return Vector__isVector(x1);
    });
}

function $partial_0_1$ParserCombinator__item(){
    return (function(x1){
        return ParserCombinator__item(x1);
    });
}

function $partial_0_1$Lists__listAppend(){
    return (function(x1){
        return Lists__listAppend(x1);
    });
}

function $partial_0_1$Lists__listLength(){
    return (function(x1){
        return Lists__listLength(x1);
    });
}

function $partial_0_1$Lists__listMember(){
    return (function(x1){
        return Lists__listMember(x1);
    });
}

function $partial_0_1$Lists__listReverse(){
    return (function(x1){
        return Lists__listReverse(x1);
    });
}

function $partial_0_1$Strings__makeString(){
    return (function(x1){
        return Strings__makeString(x1);
    });
}

function $partial_0_1$Bools__not(){
    return (function(x1){
        return Bools__not(x1);
    });
}

function $partial_0_1$Numbers__numMod(){
    return (function(x1){
        return Numbers__numMod(x1);
    });
}

function $partial_0_1$Numbers__numQuotient(){
    return (function(x1){
        return Numbers__numQuotient(x1);
    });
}

function $partial_0_1$Numbers__numRem(){
    return (function(x1){
        return Numbers__numRem(x1);
    });
}

function $partial_0_1$Numbers__numSub(){
    return (function(x1){
        return Numbers__numSub(x1);
    });
}

function $partial_0_1$Numbers__numToString(){
    return (function(x1){
        return Numbers__numToString(x1);
    });
}

function $partial_0_1$ParseNumber__octConverter(){
    return (function(x1){
        return ParseNumber__octConverter(x1);
    });
}

function $partial_0_1$Bools__or(){
    return (function(x1){
        return Bools__or(x1);
    });
}

function $partial_0_1$ParseNumber__parseComplexBase(){
    return (function(x1){
        return ParseNumber__parseComplexBase(x1);
    });
}

function $partial_0_1$ParseNumber__parseFloatBase(){
    return (function(x1){
        return ParseNumber__parseFloatBase(x1);
    });
}

function $partial_0_1$ParseNumber__parseIntegerBase(){
    return (function(x1){
        return ParseNumber__parseIntegerBase(x1);
    });
}

function $partial_0_1$ParseNumber__parseRationalBase(){
    return (function(x1){
        return ParseNumber__parseRationalBase(x1);
    });
}

function $partial_2_3$Prelude__Show__protectEsc(x1, x2){
    return (function(x3){
        return Prelude__Show__protectEsc(x1, x2, x3);
    });
}

function $partial_1_3$Ratio__rationalAdd(x1){
    return (function(x2){
        return (function(x3){
            return Ratio__rationalAdd(x1, x2, x3);
        });
    });
}

function $partial_1_3$Ratio__rationalDiv(x1){
    return (function(x2){
        return (function(x3){
            return Ratio__rationalDiv(x1, x2, x3);
        });
    });
}

function $partial_1_3$Ratio__rationalMul(x1){
    return (function(x2){
        return (function(x3){
            return Ratio__rationalMul(x1, x2, x3);
        });
    });
}

function $partial_1_3$Ratio__rationalSub(x1){
    return (function(x2){
        return (function(x3){
            return Ratio__rationalSub(x1, x2, x3);
        });
    });
}

function $partial_4_5$Repl__readOrThrow(x1, x2, x3, x4){
    return (function(x5){
        return Repl__readOrThrow(x1, x2, x3, x4, x5);
    });
}

function $partial_0_1$DataTypes__showVal(){
    return (function(x1){
        return DataTypes__showVal(x1);
    });
}

function $partial_0_1$Strings__strAppend(){
    return (function(x1){
        return Strings__strAppend(x1);
    });
}

function $partial_0_1$Strings__strLen(){
    return (function(x1){
        return Strings__strLen(x1);
    });
}

function $partial_0_1$Strings__stringRef(){
    return (function(x1){
        return Strings__stringRef(x1);
    });
}

function $partial_0_1$Strings__stringToSymbol(){
    return (function(x1){
        return Strings__stringToSymbol(x1);
    });
}

function $partial_0_1$Strings__substring(){
    return (function(x1){
        return Strings__substring(x1);
    });
}

function $partial_0_1$Symbols__symbolToString(){
    return (function(x1){
        return Symbols__symbolToString(x1);
    });
}

function $partial_2_3$ParserCombinator__try(x1, x2){
    return (function(x3){
        return ParserCombinator__try(x1, x2, x3);
    });
}

function $partial_2_3$Numbers__unaryTrig(x1, x2){
    return (function(x3){
        return Numbers__unaryTrig(x1, x2, x3);
    });
}

function $partial_0_1$Strings__unpackStr(){
    return (function(x1){
        return Strings__unpackStr(x1);
    });
}

function $partial_0_1$Vector__vectorLength(){
    return (function(x1){
        return Vector__vectorLength(x1);
    });
}

function $partial_0_1$Vector__vectorRef(){
    return (function(x1){
        return Vector__vectorRef(x1);
    });
}

function $partial_0_1$Lists___123_accessors_95_0_125_(){
    return (function(x1){
        return Lists___123_accessors_95_0_125_(x1);
    });
}

function $partial_0_2$Eval___123_apply_39__95_1_125_(){
    return (function(x1){
        return (function(x2){
            return Eval___123_apply_39__95_1_125_(x1, x2);
        });
    });
}

function $partial_0_1$Eval___123_apply_39__95_3_125_(){
    return (function(x1){
        return Eval___123_apply_39__95_3_125_(x1);
    });
}

function $partial_2_3$Eval___123_apply_39__95_4_125_(x1, x2){
    return (function(x3){
        return Eval___123_apply_39__95_4_125_(x1, x2, x3);
    });
}

function $partial_0_1$Parse___123_bracketed_95_6_125_(){
    return (function(x1){
        return Parse___123_bracketed_95_6_125_(x1);
    });
}

function $partial_0_1$Parse___123_bracketed_95_7_125_(){
    return (function(x1){
        return Parse___123_bracketed_95_7_125_(x1);
    });
}

function $partial_0_1$Parse___123_bracketed_95_8_125_(){
    return (function(x1){
        return Parse___123_bracketed_95_8_125_(x1);
    });
}

function $partial_1_3$Parse___123_bracketed_95_9_125_(x1){
    return (function(x2){
        return (function(x3){
            return Parse___123_bracketed_95_9_125_(x1, x2, x3);
        });
    });
}

function $partial_1_2$Parse___123_bracketed_95_10_125_(x1){
    return (function(x2){
        return Parse___123_bracketed_95_10_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_bracketed_95_11_125_(x1){
    return (function(x2){
        return Parse___123_bracketed_95_11_125_(x1, x2);
    });
}

function $partial_0_1$Lists___123_cons_95_14_125_(){
    return (function(x1){
        return Lists___123_cons_95_14_125_(x1);
    });
}

function $partial_1_2$ParserCombinator___123_endBy_95_20_125_(x1){
    return (function(x2){
        return ParserCombinator___123_endBy_95_20_125_(x1, x2);
    });
}

function $partial_2_3$Eval___123_ensureAtoms_95_21_125_(x1, x2){
    return (function(x3){
        return Eval___123_ensureAtoms_95_21_125_(x1, x2, x3);
    });
}

function $partial_0_2$Primitives___123_eqv_95_22_125_(){
    return (function(x1){
        return (function(x2){
            return Primitives___123_eqv_95_22_125_(x1, x2);
        });
    });
}

function $partial_2_3$Eval___123_eval_95_23_125_(x1, x2){
    return (function(x3){
        return Eval___123_eval_95_23_125_(x1, x2, x3);
    });
}

function $partial_0_1$Eval___123_eval_95_24_125_(){
    return (function(x1){
        return Eval___123_eval_95_24_125_(x1);
    });
}

function $partial_0_1$Eval___123_eval_95_25_125_(){
    return (function(x1){
        return Eval___123_eval_95_25_125_(x1);
    });
}

function $partial_2_3$Eval___123_eval_95_26_125_(x1, x2){
    return (function(x3){
        return Eval___123_eval_95_26_125_(x1, x2, x3);
    });
}

function $partial_2_3$Eval___123_eval_95_27_125_(x1, x2){
    return (function(x3){
        return Eval___123_eval_95_27_125_(x1, x2, x3);
    });
}

function $partial_3_4$Eval___123_eval_95_28_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_28_125_(x1, x2, x3, x4);
    });
}

function $partial_4_5$Eval___123_eval_95_29_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_29_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_3_4$Eval___123_eval_95_33_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_33_125_(x1, x2, x3, x4);
    });
}

function $partial_4_5$Eval___123_eval_95_34_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_34_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_3_4$Eval___123_eval_95_45_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_45_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$Eval___123_eval_95_46_125_(){
    return (function(x1){
        return Eval___123_eval_95_46_125_(x1);
    });
}

function $partial_3_4$Eval___123_eval_95_47_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_47_125_(x1, x2, x3, x4);
    });
}

function $partial_4_5$Eval___123_eval_95_90_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_90_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_3_4$Eval___123_eval_95_112_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_112_125_(x1, x2, x3, x4);
    });
}

function $partial_0_2$Eval___123_eval_95_124_125_(){
    return (function(x1){
        return (function(x2){
            return Eval___123_eval_95_124_125_(x1, x2);
        });
    });
}

function $partial_2_3$Eval___123_eval_95_125_125_(x1, x2){
    return (function(x3){
        return Eval___123_eval_95_125_125_(x1, x2, x3);
    });
}

function $partial_4_5$Eval___123_eval_95_126_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_126_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_4_5$Eval___123_eval_95_128_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_128_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Eval___123_eval_95_129_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Eval___123_eval_95_129_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Eval___123_eval_95_131_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_131_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_3_4$Eval___123_eval_95_142_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_142_125_(x1, x2, x3, x4);
    });
}

function $partial_4_5$Eval___123_eval_95_143_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_143_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_4_5$Eval___123_eval_95_145_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_145_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Eval___123_eval_95_146_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Eval___123_eval_95_146_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Eval___123_eval_95_148_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_148_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_0_2$Eval___123_eval_95_160_125_(){
    return (function(x1){
        return (function(x2){
            return Eval___123_eval_95_160_125_(x1, x2);
        });
    });
}

function $partial_4_5$Eval___123_eval_95_162_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_162_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Eval___123_eval_95_163_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Eval___123_eval_95_163_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Eval___123_eval_95_164_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_164_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_4_5$Eval___123_eval_95_166_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_166_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$Eval___123_eval_95_167_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Eval___123_eval_95_167_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Eval___123_eval_95_169_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_169_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_1_2$Eval___123_eval_95_181_125_(x1){
    return (function(x2){
        return Eval___123_eval_95_181_125_(x1, x2);
    });
}

function $partial_3_4$Eval___123_eval_95_203_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_eval_95_203_125_(x1, x2, x3, x4);
    });
}

function $partial_5_6$Eval___123_eval_95_225_125_(x1, x2, x3, x4, x5){
    return (function(x6){
        return Eval___123_eval_95_225_125_(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$Eval___123_eval_95_226_125_(x1, x2, x3, x4){
    return (function(x5){
        return Eval___123_eval_95_226_125_(x1, x2, x3, x4, x5);
    });
}

function $partial_1_2$Eval___123_evalArgs_95_257_125_(x1){
    return (function(x2){
        return Eval___123_evalArgs_95_257_125_(x1, x2);
    });
}

function $partial_3_4$Eval___123_evalArgs_95_258_125_(x1, x2, x3){
    return (function(x4){
        return Eval___123_evalArgs_95_258_125_(x1, x2, x3, x4);
    });
}

function $partial_2_3$Repl___123_evalExprList_95_260_125_(x1, x2){
    return (function(x3){
        return Repl___123_evalExprList_95_260_125_(x1, x2, x3);
    });
}

function $partial_0_2$Data__SortedMap___123_fromList_95_264_125_(){
    return (function(x1){
        return (function(x2){
            return Data__SortedMap___123_fromList_95_264_125_(x1, x2);
        });
    });
}

function $partial_1_2$Eval___123_getHeads_95_266_125_(x1){
    return (function(x2){
        return Eval___123_getHeads_95_266_125_(x1, x2);
    });
}

function $partial_1_2$Eval___123_getTails_95_268_125_(x1){
    return (function(x2){
        return Eval___123_getTails_95_268_125_(x1, x2);
    });
}

function $partial_0_5$Util___123_initEnv_39__95_270_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return Util___123_initEnv_39__95_270_125_(x1, x2, x3, x4, x5);
                    });
                });
            });
        });
    });
}

function $partial_0_3$Util___123_initEnv_39__95_271_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Util___123_initEnv_39__95_271_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_5$Util___123_initEnv_39__95_272_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return Util___123_initEnv_39__95_272_125_(x1, x2, x3, x4, x5);
                    });
                });
            });
        });
    });
}

function $partial_0_2$Util___123_initEnv_39__95_273_125_(){
    return (function(x1){
        return (function(x2){
            return Util___123_initEnv_39__95_273_125_(x1, x2);
        });
    });
}

function $partial_0_2$Util___123_initEnv_39__95_274_125_(){
    return (function(x1){
        return (function(x2){
            return Util___123_initEnv_39__95_274_125_(x1, x2);
        });
    });
}

function $partial_0_2$Util___123_initEnv_39__95_275_125_(){
    return (function(x1){
        return (function(x2){
            return Util___123_initEnv_39__95_275_125_(x1, x2);
        });
    });
}

function $partial_0_1$Lists___123_listPrimitives_95_276_125_(){
    return (function(x1){
        return Lists___123_listPrimitives_95_276_125_(x1);
    });
}

function $partial_0_1$ParserCombinator___123_many_39__95_277_125_(){
    return (function(x1){
        return ParserCombinator___123_many_39__95_277_125_(x1);
    });
}

function $partial_1_3$ParserCombinator___123_many1_95_278_125_(x1){
    return (function(x2){
        return (function(x3){
            return ParserCombinator___123_many1_95_278_125_(x1, x2, x3);
        });
    });
}

function $partial_1_2$ParserCombinator___123_many1_95_279_125_(x1){
    return (function(x2){
        return ParserCombinator___123_many1_95_279_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_matchBracket_95_280_125_(){
    return (function(x1){
        return Parse___123_matchBracket_95_280_125_(x1);
    });
}

function $partial_0_1$Parse___123_matchBracket_95_281_125_(){
    return (function(x1){
        return Parse___123_matchBracket_95_281_125_(x1);
    });
}

function $partial_0_1$Parse___123_matchBracket_95_282_125_(){
    return (function(x1){
        return Parse___123_matchBracket_95_282_125_(x1);
    });
}

function $partial_0_2$Numbers___123_numCast_95_289_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_289_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_290_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_290_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_292_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_292_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_293_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_293_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_294_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_294_125_(x1, x2);
        });
    });
}

function $partial_0_1$Numbers___123_numCast_95_298_125_(){
    return (function(x1){
        return Numbers___123_numCast_95_298_125_(x1);
    });
}

function $partial_0_2$Numbers___123_numCast_95_300_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_300_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_301_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_301_125_(x1, x2);
        });
    });
}

function $partial_0_2$Numbers___123_numCast_95_305_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCast_95_305_125_(x1, x2);
        });
    });
}

function $partial_0_1$Numbers___123_numCos_95_323_125_(){
    return (function(x1){
        return Numbers___123_numCos_95_323_125_(x1);
    });
}

function $partial_0_2$Numbers___123_numCos_95_324_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numCos_95_324_125_(x1, x2);
        });
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_325_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_325_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_326_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_326_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_327_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_327_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_328_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_328_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_329_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_329_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_330_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_330_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_331_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_331_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_332_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_332_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_333_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_333_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_334_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_334_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_335_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_335_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_336_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_336_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numPrimitives_95_337_125_(){
    return (function(x1){
        return Numbers___123_numPrimitives_95_337_125_(x1);
    });
}

function $partial_0_1$Numbers___123_numSine_95_338_125_(){
    return (function(x1){
        return Numbers___123_numSine_95_338_125_(x1);
    });
}

function $partial_0_2$Numbers___123_numSine_95_339_125_(){
    return (function(x1){
        return (function(x2){
            return Numbers___123_numSine_95_339_125_(x1, x2);
        });
    });
}

function $partial_1_2$ParserCombinator___123_oneOf_95_343_125_(x1){
    return (function(x2){
        return ParserCombinator___123_oneOf_95_343_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseAtom_95_344_125_(){
    return (function(x1){
        return Parse___123_parseAtom_95_344_125_(x1);
    });
}

function $partial_1_2$Parse___123_parseAtom_95_346_125_(x1){
    return (function(x2){
        return Parse___123_parseAtom_95_346_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_parseAtom_95_347_125_(x1){
    return (function(x2){
        return Parse___123_parseAtom_95_347_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseAtom_95_348_125_(){
    return (function(x1){
        return Parse___123_parseAtom_95_348_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseBlockComment_95_349_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseBlockComment_95_349_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_parseBlockComment_95_350_125_(){
    return (function(x1){
        return Parse___123_parseBlockComment_95_350_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseCharacter_95_352_125_(){
    return (function(x1){
        return Parse___123_parseCharacter_95_352_125_(x1);
    });
}

function $partial_1_2$Parse___123_parseCharacter_95_354_125_(x1){
    return (function(x2){
        return Parse___123_parseCharacter_95_354_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseCharacter_95_355_125_(){
    return (function(x1){
        return Parse___123_parseCharacter_95_355_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseCharacter_95_356_125_(){
    return (function(x1){
        return Parse___123_parseCharacter_95_356_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexBinary_95_357_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexDecimal_95_360_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexHelper_95_364_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexHelper_95_364_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexHelper_95_366_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexHelper_95_366_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexHelper_95_367_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexHelper_95_367_125_(x1);
    });
}

function $partial_2_3$ParseNumber___123_parseComplexHelper_95_368_125_(x1, x2){
    return (function(x3){
        return ParseNumber___123_parseComplexHelper_95_368_125_(x1, x2, x3);
    });
}

function $partial_2_3$ParseNumber___123_parseComplexHelper_95_369_125_(x1, x2){
    return (function(x3){
        return ParseNumber___123_parseComplexHelper_95_369_125_(x1, x2, x3);
    });
}

function $partial_1_2$ParseNumber___123_parseComplexHelper_95_370_125_(x1){
    return (function(x2){
        return ParseNumber___123_parseComplexHelper_95_370_125_(x1, x2);
    });
}

function $partial_3_4$ParseNumber___123_parseComplexHelper_95_371_125_(x1, x2, x3){
    return (function(x4){
        return ParseNumber___123_parseComplexHelper_95_371_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexHex_95_372_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(){
    return (function(x1){
        return ParseNumber___123_parseComplexOctal_95_375_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseDottedList_95_378_125_(){
    return (function(x1){
        return Parse___123_parseDottedList_95_378_125_(x1);
    });
}

function $partial_2_4$Parse___123_parseDottedList_95_381_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return Parse___123_parseDottedList_95_381_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_1_2$Parse___123_parseDottedList_95_382_125_(x1){
    return (function(x2){
        return Parse___123_parseDottedList_95_382_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_parseDottedList_95_383_125_(x1){
    return (function(x2){
        return Parse___123_parseDottedList_95_383_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_parseDottedList_95_384_125_(x1){
    return (function(x2){
        return Parse___123_parseDottedList_95_384_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseDottedList_95_385_125_(){
    return (function(x1){
        return Parse___123_parseDottedList_95_385_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseDottedList_95_386_125_(){
    return (function(x1){
        return Parse___123_parseDottedList_95_386_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseFloat_95_388_125_(){
    return (function(x1){
        return ParseNumber___123_parseFloat_95_388_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseFloat_95_389_125_(){
    return (function(x1){
        return ParseNumber___123_parseFloat_95_389_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseFloatHelper_95_394_125_(){
    return (function(x1){
        return ParseNumber___123_parseFloatHelper_95_394_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseFloatHelper_95_395_125_(){
    return (function(x1){
        return ParseNumber___123_parseFloatHelper_95_395_125_(x1);
    });
}

function $partial_3_4$ParseNumber___123_parseFloatHelper_95_396_125_(x1, x2, x3){
    return (function(x4){
        return ParseNumber___123_parseFloatHelper_95_396_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$ParseNumber___123_parseFloatHelper_95_397_125_(){
    return (function(x1){
        return ParseNumber___123_parseFloatHelper_95_397_125_(x1);
    });
}

function $partial_3_4$ParseNumber___123_parseFloatHelper_95_399_125_(x1, x2, x3){
    return (function(x4){
        return ParseNumber___123_parseFloatHelper_95_399_125_(x1, x2, x3, x4);
    });
}

function $partial_0_1$ParseNumber___123_parseInteger_95_403_125_(){
    return (function(x1){
        return ParseNumber___123_parseInteger_95_403_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseIntegerHelper_95_409_125_(){
    return (function(x1){
        return ParseNumber___123_parseIntegerHelper_95_409_125_(x1);
    });
}

function $partial_2_3$ParseNumber___123_parseIntegerHelper_95_410_125_(x1, x2){
    return (function(x3){
        return ParseNumber___123_parseIntegerHelper_95_410_125_(x1, x2, x3);
    });
}

function $partial_2_3$ParseNumber___123_parseIntegerHelper_95_413_125_(x1, x2){
    return (function(x3){
        return ParseNumber___123_parseIntegerHelper_95_413_125_(x1, x2, x3);
    });
}

function $partial_0_1$Parse___123_parseLineComment_95_415_125_(){
    return (function(x1){
        return Parse___123_parseLineComment_95_415_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseLineComment_95_416_125_(){
    return (function(x1){
        return Parse___123_parseLineComment_95_416_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseLineComment_95_418_125_(){
    return (function(x1){
        return Parse___123_parseLineComment_95_418_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseList_95_419_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseList_95_419_125_(x1, x2);
        });
    });
}

function $partial_0_1$ParseNumber___123_parseNumber_95_421_125_(){
    return (function(x1){
        return ParseNumber___123_parseNumber_95_421_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseQuoted_95_422_125_(){
    return (function(x1){
        return Parse___123_parseQuoted_95_422_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseQuoted_95_423_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseQuoted_95_423_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_parseQuoted_95_424_125_(){
    return (function(x1){
        return Parse___123_parseQuoted_95_424_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseRational_95_427_125_(){
    return (function(x1){
        return ParseNumber___123_parseRational_95_427_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseRationalHelper_95_433_125_(){
    return (function(x1){
        return ParseNumber___123_parseRationalHelper_95_433_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseRationalHelper_95_434_125_(){
    return (function(x1){
        return ParseNumber___123_parseRationalHelper_95_434_125_(x1);
    });
}

function $partial_0_1$ParseNumber___123_parseRationalHelper_95_436_125_(){
    return (function(x1){
        return ParseNumber___123_parseRationalHelper_95_436_125_(x1);
    });
}

function $partial_1_2$ParseNumber___123_parseRationalHelper_95_454_125_(x1){
    return (function(x2){
        return ParseNumber___123_parseRationalHelper_95_454_125_(x1, x2);
    });
}

function $partial_1_2$ParseNumber___123_parseRationalHelper_95_455_125_(x1){
    return (function(x2){
        return ParseNumber___123_parseRationalHelper_95_455_125_(x1, x2);
    });
}

function $partial_2_3$ParseNumber___123_parseRationalHelper_95_456_125_(x1, x2){
    return (function(x3){
        return ParseNumber___123_parseRationalHelper_95_456_125_(x1, x2, x3);
    });
}

function $partial_1_2$ParseNumber___123_parseRationalHelper_95_457_125_(x1){
    return (function(x2){
        return ParseNumber___123_parseRationalHelper_95_457_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseRawList_95_459_125_(){
    return (function(x1){
        return Parse___123_parseRawList_95_459_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseRawList_95_460_125_(){
    return (function(x1){
        return Parse___123_parseRawList_95_460_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseString_95_461_125_(){
    return (function(x1){
        return Parse___123_parseString_95_461_125_(x1);
    });
}

function $partial_1_3$Parse___123_parseString_95_464_125_(x1){
    return (function(x2){
        return (function(x3){
            return Parse___123_parseString_95_464_125_(x1, x2, x3);
        });
    });
}

function $partial_0_1$Parse___123_parseString_95_465_125_(){
    return (function(x1){
        return Parse___123_parseString_95_465_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseString_95_466_125_(){
    return (function(x1){
        return Parse___123_parseString_95_466_125_(x1);
    });
}

function $partial_3_4$Parse___123_parseTwoDot_95_469_125_(x1, x2, x3){
    return (function(x4){
        return Parse___123_parseTwoDot_95_469_125_(x1, x2, x3, x4);
    });
}

function $partial_3_4$Parse___123_parseTwoDot_95_470_125_(x1, x2, x3){
    return (function(x4){
        return Parse___123_parseTwoDot_95_470_125_(x1, x2, x3, x4);
    });
}

function $partial_2_3$Parse___123_parseTwoDot_95_471_125_(x1, x2){
    return (function(x3){
        return Parse___123_parseTwoDot_95_471_125_(x1, x2, x3);
    });
}

function $partial_2_3$Parse___123_parseTwoDot_95_472_125_(x1, x2){
    return (function(x3){
        return Parse___123_parseTwoDot_95_472_125_(x1, x2, x3);
    });
}

function $partial_2_3$Parse___123_parseTwoDot_95_473_125_(x1, x2){
    return (function(x3){
        return Parse___123_parseTwoDot_95_473_125_(x1, x2, x3);
    });
}

function $partial_2_3$Parse___123_parseTwoDot_95_474_125_(x1, x2){
    return (function(x3){
        return Parse___123_parseTwoDot_95_474_125_(x1, x2, x3);
    });
}

function $partial_1_2$Parse___123_parseTwoDot_95_475_125_(x1){
    return (function(x2){
        return Parse___123_parseTwoDot_95_475_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_parseTwoDot_95_476_125_(x1){
    return (function(x2){
        return Parse___123_parseTwoDot_95_476_125_(x1, x2);
    });
}

function $partial_1_2$Parse___123_parseTwoDot_95_477_125_(x1){
    return (function(x2){
        return Parse___123_parseTwoDot_95_477_125_(x1, x2);
    });
}

function $partial_0_1$Parse___123_parseTwoDot_95_478_125_(){
    return (function(x1){
        return Parse___123_parseTwoDot_95_478_125_(x1);
    });
}

function $partial_0_1$Parse___123_parseTwoDot_95_479_125_(){
    return (function(x1){
        return Parse___123_parseTwoDot_95_479_125_(x1);
    });
}

function $partial_0_2$Parse___123_parseVector_95_481_125_(){
    return (function(x1){
        return (function(x2){
            return Parse___123_parseVector_95_481_125_(x1, x2);
        });
    });
}

function $partial_0_1$Parse___123_parseVector_95_482_125_(){
    return (function(x1){
        return Parse___123_parseVector_95_482_125_(x1);
    });
}

function $partial_0_1$Eval___123_primitiveBindings_95_483_125_(){
    return (function(x1){
        return Eval___123_primitiveBindings_95_483_125_(x1);
    });
}

function $partial_0_1$Primitives___123_primitives_95_484_125_(){
    return (function(x1){
        return Primitives___123_primitives_95_484_125_(x1);
    });
}

function $partial_0_1$Repl___123_readExprList_95_485_125_(){
    return (function(x1){
        return Repl___123_readExprList_95_485_125_(x1);
    });
}

function $partial_1_2$ParserCombinator___123_rej_95_486_125_(x1){
    return (function(x2){
        return ParserCombinator___123_rej_95_486_125_(x1, x2);
    });
}

function $partial_1_2$ParserCombinator___123_rej_95_487_125_(x1){
    return (function(x2){
        return ParserCombinator___123_rej_95_487_125_(x1, x2);
    });
}

function $partial_0_3$Main___123_replEval_95_488_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_replEval_95_488_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_2$Main___123_replEval_95_489_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_489_125_(x1, x2);
        });
    });
}

function $partial_0_2$Main___123_replEval_95_490_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_490_125_(x1, x2);
        });
    });
}

function $partial_0_2$Main___123_replEval_95_491_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_491_125_(x1, x2);
        });
    });
}

function $partial_0_3$Main___123_replEval_95_492_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_replEval_95_492_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_2$Main___123_replEval_95_493_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_493_125_(x1, x2);
        });
    });
}

function $partial_0_1$Main___123_replEval_95_497_125_(){
    return (function(x1){
        return Main___123_replEval_95_497_125_(x1);
    });
}

function $partial_0_2$Main___123_replEval_95_501_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_501_125_(x1, x2);
        });
    });
}

function $partial_0_3$Main___123_replEval_95_505_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_replEval_95_505_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_3$Main___123_replEval_95_509_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_replEval_95_509_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_2$Main___123_replEval_95_513_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_513_125_(x1, x2);
        });
    });
}

function $partial_0_1$Main___123_replEval_95_540_125_(){
    return (function(x1){
        return Main___123_replEval_95_540_125_(x1);
    });
}

function $partial_0_1$Main___123_replEval_95_541_125_(){
    return (function(x1){
        return Main___123_replEval_95_541_125_(x1);
    });
}

function $partial_1_2$Main___123_replEval_95_542_125_(x1){
    return (function(x2){
        return Main___123_replEval_95_542_125_(x1, x2);
    });
}

function $partial_0_3$Main___123_replEval_95_543_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return Main___123_replEval_95_543_125_(x1, x2, x3);
            });
        });
    });
}

function $partial_0_2$Main___123_replEval_95_544_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_544_125_(x1, x2);
        });
    });
}

function $partial_0_2$Main___123_replEval_95_545_125_(){
    return (function(x1){
        return (function(x2){
            return Main___123_replEval_95_545_125_(x1, x2);
        });
    });
}

function $partial_1_2$Main___123_replEval_95_545_125_(x1){
    return (function(x2){
        return Main___123_replEval_95_545_125_(x1, x2);
    });
}

function $partial_2_4$Control__ST___123_runST_95_546_125_(x1, x2){
    return (function(x3){
        return (function(x4){
            return Control__ST___123_runST_95_546_125_(x1, x2, x3, x4);
        });
    });
}

function $partial_3_5$Control__ST___123_runST_95_547_125_(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return Control__ST___123_runST_95_547_125_(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_2_3$Control__ST___123_runST_95_548_125_(x1, x2){
    return (function(x3){
        return Control__ST___123_runST_95_548_125_(x1, x2, x3);
    });
}

function $partial_1_2$ParserCombinator___123_sat_95_551_125_(x1){
    return (function(x2){
        return ParserCombinator___123_sat_95_551_125_(x1, x2);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_553_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_553_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_554_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_554_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_555_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_555_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_556_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_556_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_557_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_557_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_558_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_558_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_559_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_559_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_560_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_560_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_561_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_561_125_(x1);
    });
}

function $partial_0_1$Prelude__Show___123_showLitChar_95_562_125_(){
    return (function(x1){
        return Prelude__Show___123_showLitChar_95_562_125_(x1);
    });
}

function $partial_1_2$Prelude__Show___123_showLitChar_95_563_125_(x1){
    return (function(x2){
        return Prelude__Show___123_showLitChar_95_563_125_(x1, x2);
    });
}

function $partial_1_2$Prelude__Show___123_showLitChar_95_564_125_(x1){
    return (function(x2){
        return Prelude__Show___123_showLitChar_95_564_125_(x1, x2);
    });
}

function $partial_0_1$DataTypes___123_showVal_95_565_125_(){
    return (function(x1){
        return DataTypes___123_showVal_95_565_125_(x1);
    });
}

function $partial_0_2$DataTypes___123_showVal_95_566_125_(){
    return (function(x1){
        return (function(x2){
            return DataTypes___123_showVal_95_566_125_(x1, x2);
        });
    });
}

function $partial_0_2$ParserCombinator___123_skipMany_95_567_125_(){
    return (function(x1){
        return (function(x2){
            return ParserCombinator___123_skipMany_95_567_125_(x1, x2);
        });
    });
}

function $partial_0_2$Strings___123_strPrimitives_95_570_125_(){
    return (function(x1){
        return (function(x2){
            return Strings___123_strPrimitives_95_570_125_(x1, x2);
        });
    });
}

function $partial_0_2$Strings___123_strPrimitives_95_571_125_(){
    return (function(x1){
        return (function(x2){
            return Strings___123_strPrimitives_95_571_125_(x1, x2);
        });
    });
}

function $partial_0_2$Strings___123_strPrimitives_95_573_125_(){
    return (function(x1){
        return (function(x2){
            return Strings___123_strPrimitives_95_573_125_(x1, x2);
        });
    });
}

function $partial_0_1$ParserCombinator___123_string_95_574_125_(){
    return (function(x1){
        return ParserCombinator___123_string_95_574_125_(x1);
    });
}

function $partial_1_2$ParserCombinator___123_string_95_577_125_(x1){
    return (function(x2){
        return ParserCombinator___123_string_95_577_125_(x1, x2);
    });
}

function $partial_0_1$Data__SortedMap___123_toList_95_585_125_(){
    return (function(x1){
        return Data__SortedMap___123_toList_95_585_125_(x1);
    });
}

function $partial_0_1$Prelude__Strings___123_unlines_95_586_125_(){
    return (function(x1){
        return Prelude__Strings___123_unlines_95_586_125_(x1);
    });
}

function $partial_0_1$Prelude__Strings___123_unwords_95_587_125_(){
    return (function(x1){
        return Prelude__Strings___123_unwords_95_587_125_(x1);
    });
}

function $partial_0_2$Prelude__Strings___123_unwords_95_588_125_(){
    return (function(x1){
        return (function(x2){
            return Prelude__Strings___123_unwords_95_588_125_(x1, x2);
        });
    });
}

function $partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_1_2$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_696_125_(x1){
    return (function(x2){
        return Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_696_125_(x1, x2);
    });
}

function $partial_1_2$Control__ST__Exception___123_Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0_95_lam_95_705_125_(x1){
    return (function(x2){
        return Control__ST__Exception___123_Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0_95_lam_95_705_125_(x1, x2);
    });
}

function $partial_1_2$Prelude__Monad___123_Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0_95_lam_95_707_125_(x1){
    return (function(x2){
        return Prelude__Monad___123_Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0_95_lam_95_707_125_(x1, x2);
    });
}

function $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(x1, x2, x3, x4){
    return (function(x5){
        return Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(x1, x2, x3, x4, x5);
    });
}

function $partial_2_3$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_newIORef_39__58_0(x1, x2){
    return (function(x3){
        return Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_newIORef_39__58_0(x1, x2, x3);
    });
}

function $partial_2_3$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_readIORef_39__58_0(x1, x2){
    return (function(x3){
        return Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_readIORef_39__58_0(x1, x2, x3);
    });
}

function $partial_3_4$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_writeIORef_39__58_0(x1, x2, x3){
    return (function(x4){
        return Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_writeIORef_39__58_0(x1, x2, x3, x4);
    });
}

function $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(x1, x2, x3, x4){
    return (function(x5){
        return Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(x1, x2, x3, x4, x5);
    });
}

function $partial_0_4$$_593_Lists__accessors_58_caaaars_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return $_593_Lists__accessors_58_caaaars_58_0_95_lam(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_2$$_594_Lists__accessors_58_caaaars_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_594_Lists__accessors_58_caaaars_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_1_3$$_595_Lists__accessors_58_caaaars_58_0_95_lam(x1){
    return (function(x2){
        return (function(x3){
            return $_595_Lists__accessors_58_caaaars_58_0_95_lam(x1, x2, x3);
        });
    });
}

function $partial_0_4$$_596_Lists__accessors_58_caaaars_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return $_596_Lists__accessors_58_caaaars_58_0_95_lam(x1, x2, x3, x4);
                });
            });
        });
    });
}

function $partial_0_3$$_605_Lists__accessors_58_makeAccessor_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return $_605_Lists__accessors_58_makeAccessor_58_0_95_lam(x1, x2, x3);
            });
        });
    });
}

function $partial_0_5$$_606_Util__bindVars_39__58_bindHelper_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return $_606_Util__bindVars_39__58_bindHelper_58_0_95_lam(x1, x2, x3, x4, x5);
                    });
                });
            });
        });
    });
}

function $partial_0_5$$_608_Util__bindVars_39__58_bindHelper_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return (function(x3){
                return (function(x4){
                    return (function(x5){
                        return $_608_Util__bindVars_39__58_bindHelper_58_0_95_lam(x1, x2, x3, x4, x5);
                    });
                });
            });
        });
    });
}

function $partial_3_5$$_615_Util__defineVar_39__58_defineHelper_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return $_615_Util__defineVar_39__58_defineHelper_58_0_95_lam(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_3_5$$_616_Util__defineVar_39__58_defineHelper_58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return (function(x5){
            return $_616_Util__defineVar_39__58_defineHelper_58_0_95_lam(x1, x2, x3, x4, x5);
        });
    });
}

function $partial_2_3$$_618_Repl__evalExprList_58_traverse_39__58_0_95_lam(x1, x2){
    return (function(x3){
        return $_618_Repl__evalExprList_58_traverse_39__58_0_95_lam(x1, x2, x3);
    });
}

function $partial_0_2$$_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_0_2$$_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_0_1$$_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(){
    return (function(x1){
        return $_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(x1);
    });
}

function $partial_4_6$$_671_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4){
    return (function(x5){
        return (function(x6){
            return $_671_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4, x5, x6);
        });
    });
}

function $partial_5_6$$_672_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4, x5){
    return (function(x6){
        return $_672_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_4_5$$_673_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4){
    return (function(x5){
        return $_673_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam(x1, x2, x3, x4, x5);
    });
}

function $partial_2_3$$_674_ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0_95_lam(x1, x2){
    return (function(x3){
        return $_674_ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0_95_lam(x1, x2, x3);
    });
}

function $partial_0_1$$_676_Parse__parseString_58_escapedChar_58_0_95_lam(){
    return (function(x1){
        return $_676_Parse__parseString_58_escapedChar_58_0_95_lam(x1);
    });
}

function $partial_0_2$$_678_Parse__parseString_58_escapedChar_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_678_Parse__parseString_58_escapedChar_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_0_1$$_679_Parse__parseString_58_escapedChar_58_0_95_lam(){
    return (function(x1){
        return $_679_Parse__parseString_58_escapedChar_58_0_95_lam(x1);
    });
}

function $partial_0_2$$_680_Util__replicateM_58_loop_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_680_Util__replicateM_58_loop_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_2_3$$_683_ParserCombinator__sepBy_58_separated_58_0_95_lam(x1, x2){
    return (function(x3){
        return $_683_ParserCombinator__sepBy_58_separated_58_0_95_lam(x1, x2, x3);
    });
}

function $partial_0_2$$_684_Util__setVar_39__58_setHelper_58_0_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_684_Util__setVar_39__58_setHelper_58_0_95_lam(x1, x2);
        });
    });
}

function $partial_2_3$$_688_ParserCombinator__skipUntil_58_scan_58_0_95_lam(x1, x2){
    return (function(x3){
        return $_688_ParserCombinator__skipUntil_58_scan_58_0_95_lam(x1, x2, x3);
    });
}

function $partial_2_3$$_689_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam(x1, x2){
    return (function(x3){
        return $_689_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam(x1, x2, x3);
    });
}

function $partial_3_4$$_691_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam(x1, x2, x3){
    return (function(x4){
        return $_691_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam(x1, x2, x3, x4);
    });
}

function $partial_3_4$$_710_Eval__apply_39__58_evalBody_58_1_95_lam(x1, x2, x3){
    return (function(x4){
        return $_710_Eval__apply_39__58_evalBody_58_1_95_lam(x1, x2, x3, x4);
    });
}

function $partial_0_2$$_718_Numbers__numDiv_58_doDiv_58_1_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_718_Numbers__numDiv_58_doDiv_58_1_95_lam(x1, x2);
        });
    });
}

function $partial_0_2$$_722_Numbers__numDiv_58_doDiv_58_1_95_lam(){
    return (function(x1){
        return (function(x2){
            return $_722_Numbers__numDiv_58_doDiv_58_1_95_lam(x1, x2);
        });
    });
}

function $partial_4_5$$_745_Eval__eval_58_evalCond_58_11_95_lam(x1, x2, x3, x4){
    return (function(x5){
        return $_745_Eval__eval_58_evalCond_58_11_95_lam(x1, x2, x3, x4, x5);
    });
}

function $partial_4_5$$_746_Eval__eval_58_evalCond_58_11_95_lam(x1, x2, x3, x4){
    return (function(x5){
        return $_746_Eval__eval_58_evalCond_58_11_95_lam(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$$_750_Eval__eval_58_evalClauses_58_12_95_lam(x1, x2, x3, x4, x5){
    return (function(x6){
        return $_750_Eval__eval_58_evalClauses_58_12_95_lam(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_3_4$$_751_Eval__eval_58_inList_58_12_95_lam(x1, x2, x3){
    return (function(x4){
        return $_751_Eval__eval_58_inList_58_12_95_lam(x1, x2, x3, x4);
    });
}

function $partial_3_4$$_752_Eval__eval_58_inList_58_12_95_lam(x1, x2, x3){
    return (function(x4){
        return $_752_Eval__eval_58_inList_58_12_95_lam(x1, x2, x3, x4);
    });
}

function $partial_4_5$$_755_Eval__eval_58_buildEnv_58_23_95_lam(x1, x2, x3, x4){
    return (function(x5){
        return $_755_Eval__eval_58_buildEnv_58_23_95_lam(x1, x2, x3, x4, x5);
    });
}

function $partial_5_6$$_756_Eval__eval_58_buildEnv_58_23_95_lam(x1, x2, x3, x4, x5){
    return (function(x6){
        return $_756_Eval__eval_58_buildEnv_58_23_95_lam(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_3_4$$_758_Eval__eval_58_buildEnv_58_24_95_lam(x1, x2, x3){
    return (function(x4){
        return $_758_Eval__eval_58_buildEnv_58_24_95_lam(x1, x2, x3, x4);
    });
}

function $partial_3_4$$_759_Eval__eval_58_setRec_58_24_95_lam(x1, x2, x3){
    return (function(x4){
        return $_759_Eval__eval_58_setRec_58_24_95_lam(x1, x2, x3, x4);
    });
}

function $partial_0_1$Lists__accessors_58_identity_58_0(){
    return (function(x1){
        return Lists__accessors_58_identity_58_0(x1);
    });
}

function $partial_5_6$Util__bindVars_39__58_bindHelper_58_0(x1, x2, x3, x4, x5){
    return (function(x6){
        return Util__bindVars_39__58_bindHelper_58_0(x1, x2, x3, x4, x5, x6);
    });
}

function $partial_7_8$Util__defineVar_39__58_defineHelper_58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Util__defineVar_39__58_defineHelper_58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_6_7$Util__getVar_39__58_getHelper_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Util__getVar_39__58_getHelper_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_0_1$Numbers__numAdd_58_doAdd_58_0(){
    return (function(x1){
        return Numbers__numAdd_58_doAdd_58_0(x1);
    });
}

function $partial_7_8$Util__setVar_39__58_setHelper_58_0(x1, x2, x3, x4, x5, x6, x7){
    return (function(x8){
        return Util__setVar_39__58_setHelper_58_0(x1, x2, x3, x4, x5, x6, x7, x8);
    });
}

function $partial_6_7$Util__showEnv_39__58_printEnv_58_0(x1, x2, x3, x4, x5, x6){
    return (function(x7){
        return Util__showEnv_39__58_printEnv_58_0(x1, x2, x3, x4, x5, x6, x7);
    });
}

function $partial_2_4$Numbers__numBoolBinopEq_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopEq_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Numbers__numBoolBinopGt_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopGt_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Numbers__numBoolBinopGte_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopGte_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Numbers__numBoolBinopLt_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopLt_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Numbers__numBoolBinopLte_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopLte_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_4$Numbers__numBoolBinopNeq_58_fn_58_1(x1, x2){
    return (function(x3){
        return (function(x4){
            return Numbers__numBoolBinopNeq_58_fn_58_1(x1, x2, x3, x4);
        });
    });
}

function $partial_2_3$Numbers__numDiv_58_doDiv_58_1(x1, x2){
    return (function(x3){
        return Numbers__numDiv_58_doDiv_58_1(x1, x2, x3);
    });
}

function $partial_1_2$Numbers__numMul_58_doMul_58_1(x1){
    return (function(x2){
        return Numbers__numMul_58_doMul_58_1(x1, x2);
    });
}

const $HC_0_0$MkUnit = ({type: 0});
function $HC_7_0$Ratio_____37_($1, $2, $3, $4, $5, $6, $7){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
    this.$6 = $6;
    this.$7 = $7;
}

function $HC_2_0$Data__Complex___58__43_($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Prelude__List___58__58_($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_2$DataTypes__BadSpecialForm($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_1$Control__ST__Bind($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_1$Data__SortedMap__Branch2($1, $2, $3){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_5_2$Data__SortedMap__Branch3($1, $2, $3, $4, $5){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
}

function $HC_2_10$Control__ST__Call($1, $2){
    this.type = 10;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_6$DataTypes__Default($1){
    this.type = 6;
    this.$1 = $1;
}

function $HC_1_0$Data__SortedMap__Empty($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_2_1$Environment__Frame($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_0$Environment__Global($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Maybe__Just($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_0$Data__SortedMap__Leaf($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_0$Prelude__Either__Left($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_2_2$Control__ST__Lift($1, $2){
    this.type = 2;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_1$DataTypes__LispAtom($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_10$DataTypes__LispBool($1){
    this.type = 10;
    this.$1 = $1;
}

function $HC_1_9$DataTypes__LispCharacter($1){
    this.type = 9;
    this.$1 = $1;
}

function $HC_1_6$DataTypes__LispComplex($1){
    this.type = 6;
    this.$1 = $1;
}

function $HC_2_3$DataTypes__LispDottedList($1, $2){
    this.type = 3;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_5$DataTypes__LispFloat($1){
    this.type = 5;
    this.$1 = $1;
}

function $HC_5_12$DataTypes__LispFunc($1, $2, $3, $4, $5){
    this.type = 12;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
}

function $HC_1_4$DataTypes__LispInteger($1){
    this.type = 4;
    this.$1 = $1;
}

function $HC_1_2$DataTypes__LispList($1){
    this.type = 2;
    this.$1 = $1;
}

function $HC_1_11$DataTypes__LispPrimitiveFunc($1){
    this.type = 11;
    this.$1 = $1;
}

function $HC_1_7$DataTypes__LispRational($1){
    this.type = 7;
    this.$1 = $1;
}

function $HC_1_8$DataTypes__LispString($1){
    this.type = 8;
    this.$1 = $1;
}

function $HC_2_0$DataTypes__LispVector($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_13$DataTypes__LispVoid = ({type: 13});
function $HC_2_1$Data__SortedMap__M($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_0$DataTypes__Min($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_2_1$DataTypes__MinMax($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_2_0$Builtins__MkPair($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Control__ST__Env__Nil = ({type: 0});
const $HC_0_0$Prelude__List__Nil = ({type: 0});
const $HC_0_1$Prelude__Basics__No = ({type: 1});
const $HC_0_0$Prelude__Maybe__Nothing = ({type: 0});
function $HC_3_0$DataTypes__NumArgs($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

const $HC_0_0$Prelude__Show__Open = ({type: 0});
function $HC_1_5$DataTypes__ParseError($1){
    this.type = 5;
    this.$1 = $1;
}

function $HC_1_0$ParserCombinator__ParseError($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_1$ParserCombinator__ParseSuccess($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_1_0$Control__ST__Pure($1){
    this.type = 0;
    this.$1 = $1;
}

function $HC_1_1$Prelude__Either__Right($1){
    this.type = 1;
    this.$1 = $1;
}

function $HC_2_1$Prelude__Strings__StrCons($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

const $HC_0_0$Prelude__Strings__StrNil = ({type: 0});
const $HC_0_0$Control__ST__SubNil = ({type: 0});
function $HC_2_1$DataTypes__TypeMismatch($1, $2){
    this.type = 1;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_1_4$Prelude__Show__User($1){
    this.type = 4;
    this.$1 = $1;
}

const $HC_0_0$Prelude__Basics__Yes = ({type: 0});
function $HC_2_0$Prelude__Interfaces__Abs_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Prelude__Applicative__Applicative_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$DataTypes__Context_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_6_0$Environment__Envir_95_ictor($1, $2, $3, $4, $5, $6){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
    this.$4 = $4;
    this.$5 = $5;
    this.$6 = $6;
}

function $HC_2_0$Prelude__Interfaces__Fractional_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Data__IORef__HasReference_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$Prelude__Interfaces__Integral_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Prelude__Interfaces__Neg_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

function $HC_3_0$Prelude__Interfaces__Num_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_3_0$Prelude__Interfaces__Ord_95_ictor($1, $2, $3){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
    this.$3 = $3;
}

function $HC_2_0$Prelude__Show__Show_95_ictor($1, $2){
    this.type = 0;
    this.$1 = $1;
    this.$2 = $2;
}

// io_bind

function io_95_bind($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_k, $_5_w){
    return $_4_k($_3_arg($_5_w))($_5_w);
}

// prim__floatToStr

function prim_95__95_floatToStr($_0_arg){
    return (''+($_0_arg));
}

// prim__strCons

function prim_95__95_strCons($_0_arg, $_1_arg){
    return (($_0_arg)+($_1_arg));
}

// prim__toStrBigInt

function prim_95__95_toStrBigInt($_0_arg){
    return (($_0_arg).toString());
}

// prim__toStrInt

function prim_95__95_toStrInt($_0_arg){
    return (''+($_0_arg));
}

// Prelude.List.++

function Prelude__List___43__43_($_0_arg, $_1_arg, $_2_arg){
    
    if(($_1_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, Prelude__List___43__43_(null, $_1_arg.$2, $_2_arg));
    } else {
        return $_2_arg;
    }
}

// Ratio.:%

function Ratio___58__37_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $cg$1 = null;
    const $cg$3 = $_1_arg.$1;
    $cg$1 = $cg$3.$3((new $JSRTS.jsbn.BigInteger(("0"))));
    
    if($_2_arg($_7_arg)($cg$1)) {
        return $HC_0_0$Prelude__Maybe__Nothing;
    } else {
        let $cg$5 = null;
        $cg$5 = $_3_arg.$2($_6_arg);
        let $cg$6 = null;
        $cg$6 = $_3_arg.$2($_7_arg);
        const $_23_in = Ratio__gcd_58_gcd_39__58_0(null, null, null, $_1_arg, null, $_2_arg, $cg$5, $cg$6);
        let $cg$7 = null;
        $cg$7 = $_1_arg.$2($_6_arg)($_23_in);
        let $cg$8 = null;
        $cg$8 = $_1_arg.$2($_7_arg)($_23_in);
        return new $HC_1_1$Prelude__Maybe__Just(new $HC_7_0$Ratio_____37_($_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $cg$7, $cg$8));
    }
}

// ParserCombinator.<|>

function ParserCombinator___60__124__62_($_0_arg, $_1_arg, $_2_arg, $_3_inp){
    const $cg$2 = $_1_arg($_3_inp);
    if(($cg$2.type === 0)) {
        return $_2_arg($_3_inp);
    } else if(($cg$2.type === 1)) {
        const $cg$4 = $cg$2.$1;
        if(($cg$4.type === 1)) {
            const $cg$6 = $cg$4.$1;
            
            if(($cg$4.$2.type === 0)) {
                return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$6.$1, $cg$6.$2), $HC_0_0$Prelude__List__Nil));
            } else {
                return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_3_inp));
            }
        } else {
            return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_3_inp));
        }
    } else {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_3_inp));
    }
}

// Lists.accessors

function Lists__accessors(){
    return Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Lists___123_accessors_95_0_125_(), Lists__accessors_58_caaaars_58_0());
}

// Environment.addBinding

function Environment__addBinding($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_6_in){
    
    let $_11_in = null;
    $_11_in = $_2_arg.$1(null)($_3_arg.$2)($_6_in);
    return new $HC_2_0$Builtins__MkPair($_3_arg.$1, $_11_in);
}

// Bools.and

function Bools__and($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
            } else {
                const $cg$4 = $_0_arg.$1;
                if(($cg$4.type === 10)) {
                    
                    if($cg$4.$1) {
                        $_0_arg = $_0_arg.$2;
                    } else {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                    }
                } else {
                    $_0_arg = $_0_arg.$2;
                }
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
        }
    }
}

// Eval.apply'

function Eval__apply_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_2_arg.type === 12)) {
        let $cg$6 = null;
        if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0(Prelude__List__length(null, $_2_arg.$2), Prelude__List__length(null, $_3_arg))) {
            $cg$6 = false;
        } else {
            $cg$6 = (!($_2_arg.$3.type === 1));
        }
        
        
        if($cg$6) {
            
            return $_1_arg.$1(null)(null)(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(((Prelude__List__length(null, $_2_arg.$2)).intValue()|0)), Prelude__List__length(null, $_3_arg), $_3_arg));
        } else {
            let $cg$8 = null;
            const $cg$10 = $_1_arg.$3;
            $cg$8 = $cg$10.$6($_2_arg.$5)(Prelude__List___43__43_(null, Prelude__List__zipWith(null, null, null, $partial_0_2$Eval___123_apply_39__95_1_125_(), $_2_arg.$2, $_3_arg), Eval__apply_39__58_varargs_39__58_1(null, $_2_arg.$2, $_2_arg.$3, null, null, $_3_arg, null, null)));
            return new $HC_2_1$Control__ST__Bind($cg$8, $partial_2_3$Eval___123_apply_39__95_4_125_($_1_arg, $_2_arg.$4));
        }
    } else if(($_2_arg.type === 11)) {
        const $cg$4 = $_2_arg.$1($_3_arg);
        if(($cg$4.type === 0)) {
            
            return $_1_arg.$1(null)(null)($cg$4.$1);
        } else {
            return new $HC_1_0$Control__ST__Pure($cg$4.$1);
        }
    } else {
        
        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default(("application: not a procedure; " + ("expected a procedure that can be applied to arguments; given: " + DataTypes__showVal($_2_arg)))));
    }
}

// ParseNumber.binConverter

function ParseNumber__binConverter($_0_arg){
    
    if(($_0_arg === "0")) {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    } else if(($_0_arg === "1")) {
        return (new $JSRTS.jsbn.BigInteger(("1")));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_binConverter_95_5_125_();
            })();
        }));
    }
}

// Util.boolBinop

function Util__boolBinop($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    const $cg$2 = Prelude__List__index_39_(null, (new $JSRTS.jsbn.BigInteger(("0"))), $_3_arg);
    if(($cg$2.type === 1)) {
        const $cg$4 = Prelude__List__index_39_(null, (new $JSRTS.jsbn.BigInteger(("1"))), $_3_arg);
        if(($cg$4.type === 1)) {
            const $cg$6 = $_1_arg($cg$2.$1);
            if(($cg$6.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left($cg$6.$1);
            } else {
                const $cg$8 = $_1_arg($cg$4.$1);
                if(($cg$8.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left($cg$8.$1);
                } else {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($_2_arg($cg$6.$1)($cg$8.$1)));
                }
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_3_arg), $_3_arg));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_3_arg), $_3_arg));
    }
}

// Bools.boolPrimitives

function Bools__boolPrimitives(){
    return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("boolean?", $partial_0_1$Bools__isBoolean()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("and", $partial_0_1$Bools__and()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("or", $partial_0_1$Bools__or()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("not", $partial_0_1$Bools__not()), $HC_0_0$Prelude__List__Nil))));
}

// Parse.bracketed

function Parse__bracketed($_0_arg, $_1_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Parse___123_bracketed_95_6_125_()), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Parse___123_bracketed_95_7_125_()), ParserCombinator__sat($partial_0_1$Parse___123_bracketed_95_8_125_()))), $partial_1_2$Parse___123_bracketed_95_11_125_($_1_arg));
}

// Lists.car

function Lists__car($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 3)) {
            const $cg$11 = $cg$3.$1;
            if(($cg$11.type === 1)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right($cg$11.$1);
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("car expected pair, found " + DataTypes__showVal($_0_arg.$1))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else if(($cg$3.type === 2)) {
            const $cg$6 = $cg$3.$1;
            if(($cg$6.type === 1)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right($cg$6.$1);
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$6.type === 0)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in car"));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("car expected pair, found " + DataTypes__showVal($_0_arg.$1))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("car expected pair, found " + DataTypes__showVal($_0_arg.$1))));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Lists.cdr

function Lists__cdr($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 3)) {
            const $cg$13 = $cg$3.$1;
            if(($cg$13.type === 1)) {
                
                if(($cg$13.$2.type === 0)) {
                    
                    if(($_0_arg.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right($JSRTS.force($cg$3.$2));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                } else {
                    
                    if(($_0_arg.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_2_3$DataTypes__LispDottedList($cg$13.$2, new $JSRTS.Lazy((function(){
                            return (function(){
                                return Lists___123_cdr_95_12_125_($cg$3.$2);
                            })();
                        }))));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("cdr expected pair, found " + DataTypes__showVal($_0_arg.$1))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else if(($cg$3.type === 2)) {
            const $cg$6 = $cg$3.$1;
            if(($cg$6.type === 1)) {
                
                if(($cg$6.$2.type === 0)) {
                    
                    if(($_0_arg.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($HC_0_0$Prelude__List__Nil));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                } else {
                    
                    if(($_0_arg.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($cg$6.$2));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                }
            } else if(($cg$6.type === 0)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("cdr on empty list"));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("cdr expected pair, found " + DataTypes__showVal($_0_arg.$1))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("cdr expected pair, found " + DataTypes__showVal($_0_arg.$1))));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Prelude.Chars.chr

function Prelude__Chars__chr($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 0) > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === 0);
    }
    
    let $cg$2 = null;
    if($cg$1) {
        $cg$2 = (!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, 1114112) < 0)));
    } else {
        $cg$2 = false;
    }
    
    
    if($cg$2) {
        return String.fromCharCode($_0_arg);
    } else {
        return "\x00";
    }
}

// Lists.cons

function Lists__cons($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$2;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 3)) {
                
                if(($cg$3.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_3$DataTypes__LispDottedList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, $cg$5.$1), new $JSRTS.Lazy((function(){
                        return (function(){
                            return Lists___123_cdr_95_12_125_($cg$5.$2);
                        })();
                    }))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$5.type === 2)) {
                
                if(($cg$3.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, $cg$5.$1)));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($cg$3.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_3$DataTypes__LispDottedList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, $HC_0_0$Prelude__List__Nil), new $JSRTS.Lazy((function(){
                        return (function(){
                            return Lists___123_cons_95_14_125_($cg$3.$1);
                        })();
                    }))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// ParseNumber.decConverter

function ParseNumber__decConverter($_0_arg){
    
    if(($_0_arg === "0")) {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    } else if(($_0_arg === "1")) {
        return (new $JSRTS.jsbn.BigInteger(("1")));
    } else if(($_0_arg === "2")) {
        return (new $JSRTS.jsbn.BigInteger(("2")));
    } else if(($_0_arg === "3")) {
        return (new $JSRTS.jsbn.BigInteger(("3")));
    } else if(($_0_arg === "4")) {
        return (new $JSRTS.jsbn.BigInteger(("4")));
    } else if(($_0_arg === "5")) {
        return (new $JSRTS.jsbn.BigInteger(("5")));
    } else if(($_0_arg === "6")) {
        return (new $JSRTS.jsbn.BigInteger(("6")));
    } else if(($_0_arg === "7")) {
        return (new $JSRTS.jsbn.BigInteger(("7")));
    } else if(($_0_arg === "8")) {
        return (new $JSRTS.jsbn.BigInteger(("8")));
    } else if(($_0_arg === "9")) {
        return (new $JSRTS.jsbn.BigInteger(("9")));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_decConverter_95_15_125_();
            })();
        }));
    }
}

// Prelude.Interfaces.divBigInt

function Prelude__Interfaces__divBigInt($_0_arg, $_1_arg){
    
    if(((($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) ? 1|0 : 0|0) === 0)) {
        return $_0_arg.divide($_1_arg);
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Prelude__Interfaces___123_divBigInt_95_16_125_();
            })();
        }));
    }
}

// Numbers.doSub

function Numbers__doSub($_0_arg){
    
    if(($_0_arg.type === 2)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$22 = $cg$3.$2;
                if(($cg$22.type === 1)) {
                    const $cg$24 = $cg$22.$1;
                    if(($cg$24.type === 6)) {
                        
                        if(($cg$22.$2.type === 0)) {
                            const $cg$27 = $cg$24.$1;
                            let $cg$26 = null;
                            const $cg$29 = $cg$5.$1;
                            $cg$26 = new $HC_2_0$Data__Complex___58__43_(($cg$29.$1 - $cg$27.$1), ($cg$29.$2 - $cg$27.$2));
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex($cg$26));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$17 = $cg$3.$2;
                if(($cg$17.type === 1)) {
                    const $cg$19 = $cg$17.$1;
                    if(($cg$19.type === 5)) {
                        
                        if(($cg$17.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat(($cg$5.$1 - $cg$19.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$12 = $cg$3.$2;
                if(($cg$12.type === 1)) {
                    const $cg$14 = $cg$12.$1;
                    if(($cg$14.type === 4)) {
                        
                        if(($cg$12.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger($cg$5.$1.subtract($cg$14.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            return Numbers__rationalBinaryOpHelper($partial_1_3$Ratio__rationalSub(null), $cg$5.$1, $cg$9.$1, "-");
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in -"));
    }
}

// Prelude.List.drop

function Prelude__List__drop($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            return $_2_arg;
        } else {
            
            if(($_2_arg.type === 1)) {
                $_0_arg = null;
                $_1_arg = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_2_arg = $_2_arg.$2;
            } else {
                return $_2_arg;
            }
        }
    }
}

// Control.ST.dropEnv

function Control__ST__dropEnv($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    return $HC_0_0$Control__ST__Env__Nil;
}

// Lists.empty

function Lists__empty($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 2)) {
            
            if(($cg$3.$1.type === 0)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// ParserCombinator.endBy

function ParserCombinator__endBy($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return ParserCombinator__many_39_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_2_arg, $partial_1_2$ParserCombinator___123_endBy_95_20_125_($_3_arg)));
}

// Eval.ensureAtom

function Eval__ensureAtom($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_1_0$Control__ST__Pure($_2_arg);
    } else {
        
        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Type error"));
    }
}

// Eval.ensureAtoms

function Eval__ensureAtoms($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_2_1$Control__ST__Bind(Eval__ensureAtom(null, $_1_arg, $_2_arg.$1), $partial_2_3$Eval___123_ensureAtoms_95_21_125_($_1_arg, $_2_arg.$2));
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
    }
}

// Primitives.eqv

function Primitives__eqv($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            const $cg$3 = $_0_arg.$1;
            if(($cg$3.type === 1)) {
                const $cg$123 = $_0_arg.$2;
                if(($cg$123.type === 1)) {
                    const $cg$125 = $cg$123.$1;
                    if(($cg$125.type === 1)) {
                        
                        if(($cg$123.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(($cg$3.$1 == $cg$125.$1)));
                        } else {
                            const $cg$131 = $_0_arg.$2;
                            
                            if(($cg$131.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$127 = $_0_arg.$2;
                        
                        if(($cg$127.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 10)) {
                const $cg$112 = $_0_arg.$2;
                if(($cg$112.type === 1)) {
                    const $cg$114 = $cg$112.$1;
                    if(($cg$114.type === 10)) {
                        
                        if(($cg$112.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Eq_36_Bool_58__33__61__61__58_0($cg$3.$1, $cg$114.$1)));
                        } else {
                            const $cg$120 = $_0_arg.$2;
                            
                            if(($cg$120.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$116 = $_0_arg.$2;
                        
                        if(($cg$116.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 9)) {
                const $cg$101 = $_0_arg.$2;
                if(($cg$101.type === 1)) {
                    const $cg$103 = $cg$101.$1;
                    if(($cg$103.type === 9)) {
                        
                        if(($cg$101.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(($cg$3.$1 === $cg$103.$1)));
                        } else {
                            const $cg$109 = $_0_arg.$2;
                            
                            if(($cg$109.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$105 = $_0_arg.$2;
                        
                        if(($cg$105.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 6)) {
                const $cg$90 = $_0_arg.$2;
                if(($cg$90.type === 1)) {
                    const $cg$92 = $cg$90.$1;
                    if(($cg$92.type === 6)) {
                        
                        if(($cg$90.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0(null, $partial_0_2$Primitives___123_eqv_95_22_125_(), $cg$3.$1, $cg$92.$1)));
                        } else {
                            const $cg$98 = $_0_arg.$2;
                            
                            if(($cg$98.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$94 = $_0_arg.$2;
                        
                        if(($cg$94.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 3)) {
                const $cg$79 = $_0_arg.$2;
                if(($cg$79.type === 1)) {
                    const $cg$81 = $cg$79.$1;
                    if(($cg$81.type === 3)) {
                        
                        if(($cg$79.$2.type === 0)) {
                            $_0_arg = new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList(Prelude__List___43__43_(null, $cg$3.$1, new $HC_2_1$Prelude__List___58__58_($JSRTS.force($cg$3.$2), $HC_0_0$Prelude__List__Nil))), new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList(Prelude__List___43__43_(null, $cg$81.$1, new $HC_2_1$Prelude__List___58__58_($JSRTS.force($cg$81.$2), $HC_0_0$Prelude__List__Nil))), $HC_0_0$Prelude__List__Nil));
                        } else {
                            const $cg$87 = $_0_arg.$2;
                            
                            if(($cg$87.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$83 = $_0_arg.$2;
                        
                        if(($cg$83.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 5)) {
                const $cg$68 = $_0_arg.$2;
                if(($cg$68.type === 1)) {
                    const $cg$70 = $cg$68.$1;
                    if(($cg$70.type === 5)) {
                        
                        if(($cg$68.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(($cg$3.$1 === $cg$70.$1)));
                        } else {
                            const $cg$76 = $_0_arg.$2;
                            
                            if(($cg$76.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$72 = $_0_arg.$2;
                        
                        if(($cg$72.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 4)) {
                const $cg$57 = $_0_arg.$2;
                if(($cg$57.type === 1)) {
                    const $cg$59 = $cg$57.$1;
                    if(($cg$59.type === 4)) {
                        
                        if(($cg$57.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$3.$1.equals($cg$59.$1)));
                        } else {
                            const $cg$65 = $_0_arg.$2;
                            
                            if(($cg$65.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$61 = $_0_arg.$2;
                        
                        if(($cg$61.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 2)) {
                const $cg$42 = $_0_arg.$2;
                if(($cg$42.type === 1)) {
                    const $cg$44 = $cg$42.$1;
                    if(($cg$44.type === 2)) {
                        
                        if(($cg$42.$2.type === 0)) {
                            
                            if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0(Prelude__List__length(null, $cg$3.$1), Prelude__List__length(null, $cg$44.$1))) {
                                const $cg$54 = Primitives__eqv_58_eqvPairs_58_9(null, null, $cg$3.$1, $cg$44.$1);
                                if(($cg$54.type === 0)) {
                                    return new $HC_1_0$Prelude__Either__Left($cg$54.$1);
                                } else {
                                    let $cg$55 = null;
                                    if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0(Prelude__List__length(null, $cg$3.$1), Prelude__List__length(null, $cg$44.$1))) {
                                        $cg$55 = $cg$54.$1;
                                    } else {
                                        $cg$55 = false;
                                    }
                                    
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$55));
                                }
                            } else {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            }
                        } else {
                            const $cg$50 = $_0_arg.$2;
                            
                            if(($cg$50.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$46 = $_0_arg.$2;
                        
                        if(($cg$46.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 7)) {
                const $cg$19 = $_0_arg.$2;
                if(($cg$19.type === 1)) {
                    const $cg$21 = $cg$19.$1;
                    if(($cg$21.type === 7)) {
                        
                        if(($cg$19.$2.type === 0)) {
                            const $cg$30 = $cg$21.$1;
                            let $cg$29 = null;
                            const $cg$32 = $cg$3.$1;
                            const $cg$34 = $cg$30.$1;
                            let $cg$33 = null;
                            const $cg$36 = $cg$34.$1;
                            $cg$33 = $cg$36.$2($cg$32.$6)($cg$30.$7);
                            const $cg$38 = $cg$30.$1;
                            let $cg$37 = null;
                            const $cg$40 = $cg$38.$1;
                            $cg$37 = $cg$40.$2($cg$30.$6)($cg$32.$7);
                            $cg$29 = $cg$30.$2($cg$33)($cg$37);
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$29));
                        } else {
                            const $cg$27 = $_0_arg.$2;
                            
                            if(($cg$27.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$23 = $_0_arg.$2;
                        
                        if(($cg$23.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$3.type === 8)) {
                const $cg$8 = $_0_arg.$2;
                if(($cg$8.type === 1)) {
                    const $cg$10 = $cg$8.$1;
                    if(($cg$10.type === 8)) {
                        
                        if(($cg$8.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(($cg$3.$1 == $cg$10.$1)));
                        } else {
                            const $cg$16 = $_0_arg.$2;
                            
                            if(($cg$16.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$12 = $_0_arg.$2;
                        
                        if(($cg$12.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                const $cg$5 = $_0_arg.$2;
                if(($cg$5.type === 1)) {
                    
                    if(($cg$5.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
        }
    }
}

// Eval.eval

function Eval__eval($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        let $cg$209 = null;
        const $cg$211 = $_1_arg.$3;
        $cg$209 = $cg$211.$3($_2_arg)($_3_arg.$1);
        return new $HC_2_1$Control__ST__Bind($cg$209, $partial_2_3$Eval___123_eval_95_23_125_($_1_arg, $_3_arg.$1));
    } else if(($_3_arg.type === 10)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 9)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 6)) {
        const $cg$205 = $_3_arg.$1;
        let $cg$204 = null;
        $cg$204 = $cg$205.$2;
        
        if((((($cg$204 === 0.0)) ? 1|0 : 0|0) === 0)) {
            return new $HC_1_0$Control__ST__Pure($_3_arg);
        } else {
            const $cg$208 = $_3_arg.$1;
            let $cg$207 = null;
            $cg$207 = $cg$208.$1;
            return new $HC_1_0$Control__ST__Pure(new $HC_1_5$DataTypes__LispFloat($cg$207));
        }
    } else if(($_3_arg.type === 5)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 4)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 2)) {
        const $cg$9 = $_3_arg.$1;
        if(($cg$9.type === 1)) {
            const $cg$12 = $cg$9.$1;
            if(($cg$12.type === 1)) {
                const $cg$17 = $cg$12.$1;
                if(($cg$17 === "apply")) {
                    const $cg$19 = $cg$9.$2;
                    if(($cg$19.type === 1)) {
                        const $cg$24 = $cg$19.$2;
                        if(($cg$24.type === 1)) {
                            
                            if(($cg$24.$2.type === 0)) {
                                let $cg$32 = null;
                                const $cg$34 = $_1_arg.$3;
                                $cg$32 = $cg$34.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$32, $partial_4_5$Eval___123_eval_95_29_125_($_1_arg, $_2_arg, $cg$19.$1, $cg$24.$1));
                            } else {
                                let $cg$29 = null;
                                const $cg$31 = $_1_arg.$3;
                                $cg$29 = $cg$31.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$29, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else {
                            let $cg$25 = null;
                            const $cg$27 = $_1_arg.$3;
                            $cg$25 = $cg$27.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$25, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$20 = null;
                        const $cg$22 = $_1_arg.$3;
                        $cg$20 = $cg$22.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$20, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "case")) {
                    const $cg$36 = $cg$9.$2;
                    if(($cg$36.type === 1)) {
                        return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$36.$1), $partial_3_4$Eval___123_eval_95_45_125_($_2_arg, $_1_arg, $cg$36.$2));
                    } else {
                        
                        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax in: (case)"));
                    }
                } else if(($cg$17 === "cond")) {
                    return Eval__eval_58_evalCond_58_11(null, $_2_arg, null, $_1_arg, $cg$9.$2);
                } else if(($cg$17 === "define")) {
                    const $cg$39 = $cg$9.$2;
                    if(($cg$39.type === 1)) {
                        const $cg$44 = $cg$39.$1;
                        if(($cg$44.type === 1)) {
                            const $cg$75 = $cg$39.$2;
                            if(($cg$75.type === 1)) {
                                
                                if(($cg$75.$2.type === 0)) {
                                    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$75.$1), $partial_3_4$Eval___123_eval_95_47_125_($_1_arg, $_2_arg, $cg$44.$1));
                                } else {
                                    let $cg$80 = null;
                                    const $cg$82 = $_1_arg.$3;
                                    $cg$80 = $cg$82.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$80, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$76 = null;
                                const $cg$78 = $_1_arg.$3;
                                $cg$76 = $cg$78.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$76, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else if(($cg$44.type === 3)) {
                            const $cg$62 = $cg$44.$1;
                            if(($cg$62.type === 1)) {
                                const $cg$67 = $cg$62.$1;
                                if(($cg$67.type === 1)) {
                                    let $cg$71 = null;
                                    const $cg$73 = $_1_arg.$3;
                                    $cg$71 = $cg$73.$5($_2_arg)($cg$67.$1)(new $HC_5_12$DataTypes__LispFunc($cg$67.$1, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $cg$62.$2), new $HC_1_1$Prelude__Maybe__Just(DataTypes__showVal($JSRTS.force($cg$44.$2))), $cg$39.$2, $_2_arg));
                                    return new $HC_2_1$Control__ST__Bind($cg$71, $partial_0_1$Eval___123_eval_95_46_125_());
                                } else {
                                    let $cg$68 = null;
                                    const $cg$70 = $_1_arg.$3;
                                    $cg$68 = $cg$70.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$68, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$63 = null;
                                const $cg$65 = $_1_arg.$3;
                                $cg$63 = $cg$65.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$63, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else if(($cg$44.type === 2)) {
                            const $cg$49 = $cg$44.$1;
                            if(($cg$49.type === 1)) {
                                const $cg$54 = $cg$49.$1;
                                if(($cg$54.type === 1)) {
                                    let $cg$58 = null;
                                    const $cg$60 = $_1_arg.$3;
                                    $cg$58 = $cg$60.$5($_2_arg)($cg$54.$1)(new $HC_5_12$DataTypes__LispFunc($cg$54.$1, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $cg$49.$2), $HC_0_0$Prelude__Maybe__Nothing, $cg$39.$2, $_2_arg));
                                    return new $HC_2_1$Control__ST__Bind($cg$58, $partial_0_1$Eval___123_eval_95_46_125_());
                                } else {
                                    let $cg$55 = null;
                                    const $cg$57 = $_1_arg.$3;
                                    $cg$55 = $cg$57.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$55, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$50 = null;
                                const $cg$52 = $_1_arg.$3;
                                $cg$50 = $cg$52.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$50, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else {
                            let $cg$45 = null;
                            const $cg$47 = $_1_arg.$3;
                            $cg$45 = $cg$47.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$45, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$40 = null;
                        const $cg$42 = $_1_arg.$3;
                        $cg$40 = $cg$42.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$40, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "if")) {
                    const $cg$84 = $cg$9.$2;
                    if(($cg$84.type === 1)) {
                        const $cg$89 = $cg$84.$2;
                        if(($cg$89.type === 1)) {
                            const $cg$94 = $cg$89.$2;
                            if(($cg$94.type === 1)) {
                                
                                if(($cg$94.$2.type === 0)) {
                                    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$84.$1), $partial_4_5$Eval___123_eval_95_90_125_($_1_arg, $_2_arg, $cg$94.$1, $cg$89.$1));
                                } else {
                                    let $cg$99 = null;
                                    const $cg$101 = $_1_arg.$3;
                                    $cg$99 = $cg$101.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$99, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$95 = null;
                                const $cg$97 = $_1_arg.$3;
                                $cg$95 = $cg$97.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$95, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else {
                            let $cg$90 = null;
                            const $cg$92 = $_1_arg.$3;
                            $cg$90 = $cg$92.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$90, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$85 = null;
                        const $cg$87 = $_1_arg.$3;
                        $cg$85 = $cg$87.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$85, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "lambda")) {
                    const $cg$103 = $cg$9.$2;
                    if(($cg$103.type === 1)) {
                        const $cg$108 = $cg$103.$1;
                        if(($cg$108.type === 1)) {
                            return new $HC_1_0$Control__ST__Pure(new $HC_5_12$DataTypes__LispFunc("\u03bb", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $HC_0_0$Prelude__List__Nil), new $HC_1_1$Prelude__Maybe__Just(DataTypes__showVal($cg$103.$1)), $cg$103.$2, $_2_arg));
                        } else if(($cg$108.type === 3)) {
                            return new $HC_1_0$Control__ST__Pure(new $HC_5_12$DataTypes__LispFunc("\u03bb", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $cg$108.$1), new $HC_1_1$Prelude__Maybe__Just(DataTypes__showVal($JSRTS.force($cg$108.$2))), $cg$103.$2, $_2_arg));
                        } else if(($cg$108.type === 2)) {
                            let $cg$112 = null;
                            const $cg$114 = $_1_arg.$3;
                            $cg$112 = $cg$114.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$112, $partial_3_4$Eval___123_eval_95_112_125_($cg$108.$1, $cg$103.$2, $_2_arg));
                        } else {
                            let $cg$109 = null;
                            const $cg$111 = $_1_arg.$3;
                            $cg$109 = $cg$111.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$109, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$104 = null;
                        const $cg$106 = $_1_arg.$3;
                        $cg$104 = $cg$106.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$104, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "let")) {
                    const $cg$116 = $cg$9.$2;
                    if(($cg$116.type === 1)) {
                        const $cg$121 = $cg$116.$1;
                        if(($cg$121.type === 2)) {
                            return new $HC_2_1$Control__ST__Bind(Eval__getHeads(null, $_1_arg, $cg$121.$1), $partial_4_5$Eval___123_eval_95_131_125_($_1_arg, $cg$121.$1, $_2_arg, $cg$116.$2));
                        } else {
                            let $cg$122 = null;
                            const $cg$124 = $_1_arg.$3;
                            $cg$122 = $cg$124.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$122, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$117 = null;
                        const $cg$119 = $_1_arg.$3;
                        $cg$117 = $cg$119.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$117, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "let*")) {
                    const $cg$126 = $cg$9.$2;
                    if(($cg$126.type === 1)) {
                        const $cg$131 = $cg$126.$1;
                        if(($cg$131.type === 2)) {
                            return new $HC_2_1$Control__ST__Bind(Eval__getHeads(null, $_1_arg, $cg$131.$1), $partial_4_5$Eval___123_eval_95_148_125_($_1_arg, $cg$131.$1, $_2_arg, $cg$126.$2));
                        } else {
                            let $cg$132 = null;
                            const $cg$134 = $_1_arg.$3;
                            $cg$132 = $cg$134.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$132, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$127 = null;
                        const $cg$129 = $_1_arg.$3;
                        $cg$127 = $cg$129.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$127, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "letrec")) {
                    const $cg$136 = $cg$9.$2;
                    if(($cg$136.type === 1)) {
                        const $cg$141 = $cg$136.$1;
                        if(($cg$141.type === 2)) {
                            return new $HC_2_1$Control__ST__Bind(Eval__getHeads(null, $_1_arg, $cg$141.$1), $partial_4_5$Eval___123_eval_95_169_125_($_1_arg, $cg$141.$1, $_2_arg, $cg$136.$2));
                        } else {
                            let $cg$142 = null;
                            const $cg$144 = $_1_arg.$3;
                            $cg$142 = $cg$144.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$142, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$137 = null;
                        const $cg$139 = $_1_arg.$3;
                        $cg$137 = $cg$139.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$137, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "print")) {
                    const $cg$146 = $cg$9.$2;
                    if(($cg$146.type === 1)) {
                        
                        if(($cg$146.$2.type === 0)) {
                            return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$146.$1), $partial_1_2$Eval___123_eval_95_181_125_($_1_arg));
                        } else {
                            let $cg$151 = null;
                            const $cg$153 = $_1_arg.$3;
                            $cg$151 = $cg$153.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$151, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$147 = null;
                        const $cg$149 = $_1_arg.$3;
                        $cg$147 = $cg$149.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$147, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "quote")) {
                    const $cg$155 = $cg$9.$2;
                    if(($cg$155.type === 1)) {
                        
                        if(($cg$155.$2.type === 0)) {
                            return new $HC_1_0$Control__ST__Pure($cg$155.$1);
                        } else {
                            let $cg$160 = null;
                            const $cg$162 = $_1_arg.$3;
                            $cg$160 = $cg$162.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$160, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$156 = null;
                        const $cg$158 = $_1_arg.$3;
                        $cg$156 = $cg$158.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$156, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "set!")) {
                    const $cg$164 = $cg$9.$2;
                    if(($cg$164.type === 1)) {
                        const $cg$169 = $cg$164.$1;
                        if(($cg$169.type === 1)) {
                            const $cg$174 = $cg$164.$2;
                            if(($cg$174.type === 1)) {
                                
                                if(($cg$174.$2.type === 0)) {
                                    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$174.$1), $partial_3_4$Eval___123_eval_95_203_125_($_1_arg, $_2_arg, $cg$169.$1));
                                } else {
                                    let $cg$179 = null;
                                    const $cg$181 = $_1_arg.$3;
                                    $cg$179 = $cg$181.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$179, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$175 = null;
                                const $cg$177 = $_1_arg.$3;
                                $cg$175 = $cg$177.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$175, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else {
                            let $cg$170 = null;
                            const $cg$172 = $_1_arg.$3;
                            $cg$170 = $cg$172.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$170, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$165 = null;
                        const $cg$167 = $_1_arg.$3;
                        $cg$165 = $cg$167.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$165, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else if(($cg$17 === "set-car!")) {
                    const $cg$183 = $cg$9.$2;
                    if(($cg$183.type === 1)) {
                        const $cg$188 = $cg$183.$1;
                        if(($cg$188.type === 1)) {
                            const $cg$193 = $cg$183.$2;
                            if(($cg$193.type === 1)) {
                                
                                if(($cg$193.$2.type === 0)) {
                                    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $cg$193.$1), $partial_4_5$Eval___123_eval_95_226_125_($_1_arg, $_2_arg, $cg$188.$1, $cg$193.$1));
                                } else {
                                    let $cg$198 = null;
                                    const $cg$200 = $_1_arg.$3;
                                    $cg$198 = $cg$200.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                    return new $HC_2_1$Control__ST__Bind($cg$198, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                                }
                            } else {
                                let $cg$194 = null;
                                const $cg$196 = $_1_arg.$3;
                                $cg$194 = $cg$196.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                                return new $HC_2_1$Control__ST__Bind($cg$194, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                            }
                        } else {
                            let $cg$189 = null;
                            const $cg$191 = $_1_arg.$3;
                            $cg$189 = $cg$191.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                            return new $HC_2_1$Control__ST__Bind($cg$189, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                        }
                    } else {
                        let $cg$184 = null;
                        const $cg$186 = $_1_arg.$3;
                        $cg$184 = $cg$186.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                        return new $HC_2_1$Control__ST__Bind($cg$184, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                    }
                } else {
                    let $cg$201 = null;
                    const $cg$203 = $_1_arg.$3;
                    $cg$201 = $cg$203.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                    return new $HC_2_1$Control__ST__Bind($cg$201, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
                }
            } else {
                let $cg$13 = null;
                const $cg$15 = $_1_arg.$3;
                $cg$13 = $cg$15.$1(new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()))($_2_arg);
                return new $HC_2_1$Control__ST__Bind($cg$13, $partial_4_5$Eval___123_eval_95_34_125_($_1_arg, $_2_arg, $cg$9.$1, $cg$9.$2));
            }
        } else {
            
            return $_1_arg.$1(null)(null)(new $HC_2_2$DataTypes__BadSpecialForm("Unrecognized special form", $_3_arg));
        }
    } else if(($_3_arg.type === 7)) {
        const $cg$4 = $_3_arg.$1;
        let $cg$3 = null;
        $cg$3 = $cg$4.$7;
        
        if(((($cg$3.equals((new $JSRTS.jsbn.BigInteger(("1"))))) ? 1|0 : 0|0) === 0)) {
            return new $HC_1_0$Control__ST__Pure($_3_arg);
        } else {
            const $cg$7 = $_3_arg.$1;
            let $cg$6 = null;
            $cg$6 = $cg$7.$6;
            return new $HC_1_0$Control__ST__Pure(new $HC_1_4$DataTypes__LispInteger($cg$6));
        }
    } else if(($_3_arg.type === 8)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure($_3_arg);
    } else if(($_3_arg.type === 13)) {
        return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
    } else {
        
        return $_1_arg.$1(null)(null)(new $HC_2_2$DataTypes__BadSpecialForm("Unrecognized special form", $_3_arg));
    }
}

// Eval.evalArgs

function Eval__evalArgs($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $_3_arg.$1), $partial_3_4$Eval___123_evalArgs_95_258_125_($_1_arg, $_2_arg, $_3_arg.$2));
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_0$Prelude__List__Nil);
    }
}

// Repl.evalExprList

function Repl__evalExprList($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return new $HC_2_1$Control__ST__Bind(Repl__readExprList(null, $_1_arg)($_3_arg), $partial_2_3$Repl___123_evalExprList_95_260_125_($_1_arg, $_2_arg));
}

// Eval.evalList

function Eval__evalList($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        
        if(($_3_arg.$2.type === 0)) {
            return Eval__eval(null, $_1_arg, $_2_arg, $_3_arg.$1);
        } else {
            return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_1_arg, $_2_arg, $_3_arg.$1), $partial_3_4$Eval___123_eval_95_142_125_($_1_arg, $_2_arg, $_3_arg.$2));
        }
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
    }
}

// ParserCombinator.failure

function ParserCombinator__failure($_0_arg, $_1_arg, $_2_s1){
    
    if(($_2_s1 === "")) {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair($_1_arg, ""));
    } else {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair($_1_arg, $_2_s1));
    }
}

// Prelude.List.filter

function Prelude__List__filter($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            if($_1_arg($_2_arg.$1)) {
                return new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, Prelude__List__filter(null, $_1_arg, $_2_arg.$2));
            } else {
                $_0_arg = null;
                $_1_arg = $_1_arg;
                $_2_arg = $_2_arg.$2;
            }
        } else {
            return $_2_arg;
        }
    }
}

// Prelude.Strings.foldr1

function Prelude__Strings__foldr1($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        
        if(($_2_arg.$2.type === 0)) {
            return $_2_arg.$1;
        } else {
            return $_1_arg($_2_arg.$1)(Prelude__Strings__foldr1(null, $_1_arg, $_2_arg.$2));
        }
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Prelude__Strings___123_foldr1_95_263_125_();
            })();
        }));
    }
}

// Data.SortedMap.fromList

function Data__SortedMap__fromList($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0(null, null, $partial_0_2$Data__SortedMap___123_fromList_95_264_125_(), new $HC_1_0$Data__SortedMap__Empty($_2_arg), $_3_arg);
}

// Eval.getHeads

function Eval__getHeads($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        const $cg$4 = $_2_arg.$1;
        if(($cg$4.type === 2)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                return new $HC_2_1$Control__ST__Bind(Eval__getHeads(null, $_1_arg, $_2_arg.$2), $partial_1_2$Eval___123_getHeads_95_266_125_($cg$7.$1));
            } else {
                
                return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getHeads)"));
            }
        } else {
            
            return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getHeads)"));
        }
    } else if(($_2_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure(new $HC_1_2$DataTypes__LispList($HC_0_0$Prelude__List__Nil));
    } else {
        
        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getHeads)"));
    }
}

// Eval.getTails

function Eval__getTails($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 1)) {
        const $cg$4 = $_2_arg.$1;
        if(($cg$4.type === 2)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                const $cg$10 = $cg$7.$2;
                if(($cg$10.type === 1)) {
                    
                    if(($cg$10.$2.type === 0)) {
                        return new $HC_2_1$Control__ST__Bind(Eval__getTails(null, $_1_arg, $_2_arg.$2), $partial_1_2$Eval___123_getTails_95_268_125_($cg$10.$1));
                    } else {
                        
                        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getTails)"));
                    }
                } else {
                    
                    return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getTails)"));
                }
            } else {
                
                return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getTails)"));
            }
        } else {
            
            return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getTails)"));
        }
    } else if(($_2_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure(new $HC_1_2$DataTypes__LispList($HC_0_0$Prelude__List__Nil));
    } else {
        
        return $_1_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Unexpected error (getTails)"));
    }
}

// ParseNumber.hexConverter

function ParseNumber__hexConverter($_0_arg){
    let $cg$1 = null;
    if(Prelude__Chars__isLower($_0_arg)) {
        $cg$1 = String.fromCharCode(((($_0_arg).charCodeAt(0)|0) - 32));
    } else {
        $cg$1 = $_0_arg;
    }
    
    
    if(($cg$1 === "0")) {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    } else if(($cg$1 === "1")) {
        return (new $JSRTS.jsbn.BigInteger(("1")));
    } else if(($cg$1 === "2")) {
        return (new $JSRTS.jsbn.BigInteger(("2")));
    } else if(($cg$1 === "3")) {
        return (new $JSRTS.jsbn.BigInteger(("3")));
    } else if(($cg$1 === "4")) {
        return (new $JSRTS.jsbn.BigInteger(("4")));
    } else if(($cg$1 === "5")) {
        return (new $JSRTS.jsbn.BigInteger(("5")));
    } else if(($cg$1 === "6")) {
        return (new $JSRTS.jsbn.BigInteger(("6")));
    } else if(($cg$1 === "7")) {
        return (new $JSRTS.jsbn.BigInteger(("7")));
    } else if(($cg$1 === "8")) {
        return (new $JSRTS.jsbn.BigInteger(("8")));
    } else if(($cg$1 === "9")) {
        return (new $JSRTS.jsbn.BigInteger(("9")));
    } else if(($cg$1 === "A")) {
        return (new $JSRTS.jsbn.BigInteger(("10")));
    } else if(($cg$1 === "B")) {
        return (new $JSRTS.jsbn.BigInteger(("11")));
    } else if(($cg$1 === "C")) {
        return (new $JSRTS.jsbn.BigInteger(("12")));
    } else if(($cg$1 === "D")) {
        return (new $JSRTS.jsbn.BigInteger(("13")));
    } else if(($cg$1 === "E")) {
        return (new $JSRTS.jsbn.BigInteger(("14")));
    } else if(($cg$1 === "F")) {
        return (new $JSRTS.jsbn.BigInteger(("15")));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_hexConverter_95_269_125_();
            })();
        }));
    }
}

// Prelude.List.index'

function Prelude__List__index_39_($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return new $HC_1_1$Prelude__Maybe__Just($_2_arg.$1);
            } else {
                const $_5_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = null;
                $_1_arg = $_5_in;
                $_2_arg = $_2_arg.$2;
            }
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    }
}

// Util.initEnv'

function Util__initEnv_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_in){
    const $_21_in = Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_5$Util___123_initEnv_39__95_270_125_(), $partial_0_3$Util___123_initEnv_39__95_271_125_(), $partial_0_5$Util___123_initEnv_39__95_272_125_()), $partial_3_5$Environment__addBinding(null, null, $_2_arg), $_3_arg)($_4_in);
    let $_31_in = null;
    $_31_in = $_2_arg.$1(null)(Data__SortedMap__fromList(null, null, new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Util___123_initEnv_39__95_273_125_(), $partial_0_2$Util___123_initEnv_39__95_274_125_(), $partial_0_2$Util___123_initEnv_39__95_275_125_()), $_21_in))($_4_in);
    return new $HC_1_0$Environment__Global($_31_in);
}

// Data.SortedMap.insert

function Data__SortedMap__insert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 0)) {
        return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_2_arg, $_3_arg));
    } else {
        const $cg$3 = Data__SortedMap__treeInsert(null, null, $_4_arg.$1, null, $_2_arg, $_3_arg, $_4_arg.$2);
        if(($cg$3.type === 0)) {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        } else {
            return new $HC_2_1$Data__SortedMap__M($_4_arg.$1, $cg$3.$1);
        }
    }
}

// Control.IOExcept.ioe_lift

function Control__IOExcept__ioe_95_lift($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_in){
    const $_5_in = $_3_arg($_4_in);
    return new $HC_1_1$Prelude__Either__Right($_5_in);
}

// Control.IOExcept.ioe_run

function Control__IOExcept__ioe_95_run($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_in){
    const $_8_in = $_4_arg($_7_in);
    
    if(($_8_in.type === 0)) {
        return $_5_arg($_8_in.$1)($_7_in);
    } else {
        return $_6_arg($_8_in.$1)($_7_in);
    }
}

// Bools.isBoolean

function Bools__isBoolean($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 10)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Primitives.isChar

function Primitives__isChar($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 9)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Prelude.Chars.isDigit

function Prelude__Chars__isDigit($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "0") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "0");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "9") < 0)) {
            return true;
        } else {
            return ($_0_arg === "9");
        }
    } else {
        return false;
    }
}

// Numbers.isInteger

function Numbers__isInteger($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 4)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Lists.isList

function Lists__isList($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 2)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Prelude.Chars.isLower

function Prelude__Chars__isLower($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "a") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "a");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "z");
        }
    } else {
        return false;
    }
}

// Lists.isPair

function Lists__isPair($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 3)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else if(($cg$3.type === 2)) {
            
            if(($cg$3.$1.type === 0)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                } else {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                } else {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                }
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Procedures.isProcedure

function Procedures__isProcedure($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 12)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else if(($cg$3.type === 11)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Prelude.Chars.isSpace

function Prelude__Chars__isSpace($_0_arg){
    
    if((((($_0_arg === " ")) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg === "\t")) ? 1|0 : 0|0) === 0)) {
            
            if((((($_0_arg === "\r")) ? 1|0 : 0|0) === 0)) {
                
                if((((($_0_arg === "\n")) ? 1|0 : 0|0) === 0)) {
                    
                    if((((($_0_arg === "\f")) ? 1|0 : 0|0) === 0)) {
                        
                        if((((($_0_arg === "\v")) ? 1|0 : 0|0) === 0)) {
                            return ($_0_arg === "\xa0");
                        } else {
                            return true;
                        }
                    } else {
                        return true;
                    }
                } else {
                    return true;
                }
            } else {
                return true;
            }
        } else {
            return true;
        }
    } else {
        return true;
    }
}

// Strings.isString

function Strings__isString($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 8)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Symbols.isSymbol

function Symbols__isSymbol($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 1)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
    }
}

// Prelude.Chars.isUpper

function Prelude__Chars__isUpper($_0_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "A") > 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_0_arg === "A");
    }
    
    
    if($cg$1) {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "Z") < 0)) {
            return true;
        } else {
            return ($_0_arg === "Z");
        }
    } else {
        return false;
    }
}

// Vector.isVector

function Vector__isVector($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 0)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// ParserCombinator.item

function ParserCombinator__item($_0_inp){
    
    if(($_0_inp === "")) {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("\'Item\' run on empty input", ""));
    } else {
        let $cg$2 = null;
        if(($_0_inp === "")) {
            $cg$2 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the head of an empty string"));
        } else {
            $cg$2 = $_0_inp[0];
        }
        
        let $cg$3 = null;
        if(($_0_inp === "")) {
            $cg$3 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the tail of an empty string"));
        } else {
            $cg$3 = $_0_inp.slice(1);
        }
        
        return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$2, $cg$3), $HC_0_0$Prelude__List__Nil));
    }
}

// Prelude.List.last

function Prelude__List__last($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        const $cg$3 = $_1_arg.$2;
        if(($cg$3.type === 1)) {
            $_0_arg = null;
            $_1_arg = new $HC_2_1$Prelude__List___58__58_($cg$3.$1, $cg$3.$2);
            $_2_arg = null;
        } else {
            return $_1_arg.$1;
        }
    }
}

// Prelude.List.length

function Prelude__List__length($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        return Prelude__List__length(null, $_1_arg.$2).add((new $JSRTS.jsbn.BigInteger(("1"))));
    } else {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    }
}

// Lists.listAppend

function Lists__listAppend($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 2)) {
            const $cg$5 = $_0_arg.$2;
            if(($cg$5.type === 1)) {
                const $cg$7 = $cg$5.$1;
                if(($cg$7.type === 2)) {
                    
                    if(($cg$5.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(Prelude__List___43__43_(null, $cg$3.$1, $cg$7.$1)));
                    } else {
                        return Lists__listAppend_58_helper_58_1(null, $HC_0_0$Prelude__List__Nil, $_0_arg);
                    }
                } else {
                    return Lists__listAppend_58_helper_58_1(null, $HC_0_0$Prelude__List__Nil, $_0_arg);
                }
            } else {
                return Lists__listAppend_58_helper_58_1(null, $HC_0_0$Prelude__List__Nil, $_0_arg);
            }
        } else {
            return Lists__listAppend_58_helper_58_1(null, $HC_0_0$Prelude__List__Nil, $_0_arg);
        }
    } else {
        return Lists__listAppend_58_helper_58_1(null, $HC_0_0$Prelude__List__Nil, $_0_arg);
    }
}

// DataTypes.listEq

function DataTypes__listEq($_0_arg, $_1_arg){
    for(;;) {
        
        if(($_1_arg.type === 1)) {
            
            if(($_0_arg.type === 1)) {
                
                if(Prelude__Interfaces__DataTypes___64_Prelude__Interfaces__Eq_36_LispVal_58__33__61__61__58_0($_0_arg.$1, $_1_arg.$1)) {
                    $_0_arg = $_0_arg.$2;
                    $_1_arg = $_1_arg.$2;
                } else {
                    return false;
                }
            } else {
                return false;
            }
        } else if(($_1_arg.type === 0)) {
            return (!(!($_0_arg.type === 0)));
        } else {
            return false;
        }
    }
}

// Lists.listLength

function Lists__listLength($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 2)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger(Prelude__List__length(null, $cg$3.$1)));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Lists.listMember

function Lists__listMember($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$2;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 2)) {
                
                if(($cg$3.$2.type === 0)) {
                    return Lists__listMember_58_helper_58_0($_0_arg.$1, null, $cg$5.$1);
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($cg$3.$2.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $cg$3.$1));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Lists.listPrimitives

function Lists__listPrimitives(){
    return Prelude__List___43__43_(null, new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("pair?", $partial_0_1$Lists__isPair()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("car", $partial_0_1$Lists__car()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("cdr", $partial_0_1$Lists__cdr()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("cons", $partial_0_1$Lists__cons()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("empty?", $partial_0_1$Lists__empty()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("null?", $partial_0_1$Lists__empty()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("list", $partial_0_1$Lists___123_listPrimitives_95_276_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("list?", $partial_0_1$Lists__isList()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("length", $partial_0_1$Lists__listLength()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("append", $partial_0_1$Lists__listAppend()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("reverse", $partial_0_1$Lists__listReverse()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("member", $partial_0_1$Lists__listMember()), $HC_0_0$Prelude__List__Nil)))))))))))), Lists__accessors());
}

// Lists.listReverse

function Lists__listReverse($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 2)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(Prelude__List__reverseOnto(null, $HC_0_0$Prelude__List__Nil, $cg$3.$1)));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else if(($_0_arg.type === 0)) {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Strings.makeString

function Strings__makeString($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            const $cg$3 = $_0_arg.$1;
            if(($cg$3.type === 4)) {
                const $cg$5 = $_0_arg.$2;
                if(($cg$5.type === 1)) {
                    const $cg$7 = $cg$5.$1;
                    if(($cg$7.type === 9)) {
                        
                        if(($cg$5.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_8$DataTypes__LispString(Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__List__replicate(null, $cg$3.$1, $cg$7.$1))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `make-string`"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `make-string`"));
                    }
                } else if(($cg$5.type === 0)) {
                    $_0_arg = new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(0)), $HC_0_0$Prelude__List__Nil));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `make-string`"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `make-string`"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `make-string`"));
        }
    }
}

// ParserCombinator.many'

function ParserCombinator__many_39_($_0_arg, $_1_arg){
    return $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__many1(null, $_1_arg), $partial_0_1$ParserCombinator___123_many_39__95_277_125_());
}

// ParserCombinator.many1

function ParserCombinator__many1($_0_arg, $_1_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_1_arg, $partial_1_2$ParserCombinator___123_many1_95_279_125_($_1_arg));
}

// Parse.matchBracket

function Parse__matchBracket($_0_arg){
    
    if(($_0_arg === "(")) {
        return ParserCombinator__sat($partial_0_1$Parse___123_matchBracket_95_280_125_());
    } else if(($_0_arg === "[")) {
        return ParserCombinator__sat($partial_0_1$Parse___123_matchBracket_95_281_125_());
    } else if(($_0_arg === "{")) {
        return ParserCombinator__sat($partial_0_1$Parse___123_matchBracket_95_282_125_());
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Parse___123_matchBracket_95_283_125_();
            })();
        }));
    }
}

// Prelude.Interfaces.modBigInt

function Prelude__Interfaces__modBigInt($_0_arg, $_1_arg){
    
    if(((($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) ? 1|0 : 0|0) === 0)) {
        return $_0_arg.remainder($_1_arg);
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Prelude__Interfaces___123_modBigInt_95_284_125_();
            })();
        }));
    }
}

// Bools.not

function Bools__not($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 10)) {
            
            if((!$cg$3.$1)) {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else {
                
                if(($_0_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Numbers.numBoolBinop

function Numbers__numBoolBinop($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            const $cg$3 = Numbers__numCast(new $HC_2_1$Prelude__List___58__58_($_2_arg, new $HC_2_1$Prelude__List___58__58_($_3_arg.$1, $HC_0_0$Prelude__List__Nil)));
            if(($cg$3.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left($cg$3.$1);
            } else {
                const $cg$5 = $cg$3.$1;
                if(($cg$5.type === 2)) {
                    const $cg$7 = $cg$5.$1;
                    if(($cg$7.type === 1)) {
                        const $cg$9 = $cg$7.$2;
                        if(($cg$9.type === 1)) {
                            
                            if(($cg$9.$2.type === 0)) {
                                const $cg$12 = $_1_arg($cg$7.$1)($cg$9.$1);
                                if(($cg$12.type === 0)) {
                                    return $_1_arg($cg$7.$1)($cg$9.$1);
                                } else {
                                    const $cg$14 = $cg$12.$1;
                                    if(($cg$14.type === 10)) {
                                        const $cg$16 = $cg$14.$1;
                                        if((!$cg$16)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
                                        } else if($cg$16) {
                                            $_0_arg = $_0_arg;
                                            $_1_arg = $_1_arg;
                                            $_2_arg = $cg$9.$1;
                                            $_3_arg = $_3_arg.$2;
                                        } else {
                                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("Unexpected error in " + $_0_arg)));
                                        }
                                    } else {
                                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("Unexpected error in " + $_0_arg)));
                                    }
                                }
                            } else {
                                return new $JSRTS.Lazy((function(){
                                    return (function(){
                                        return Numbers___123_numBoolBinop_95_285_125_();
                                    })();
                                }));
                            }
                        } else {
                            return new $JSRTS.Lazy((function(){
                                return (function(){
                                    return Numbers___123_numBoolBinop_95_285_125_();
                                })();
                            }));
                        }
                    } else {
                        return new $JSRTS.Lazy((function(){
                            return (function(){
                                return Numbers___123_numBoolBinop_95_285_125_();
                            })();
                        }));
                    }
                } else {
                    return new $JSRTS.Lazy((function(){
                        return (function(){
                            return Numbers___123_numBoolBinop_95_285_125_();
                        })();
                    }));
                }
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
        }
    }
}

// Numbers.numCast

function Numbers__numCast($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 6)) {
            const $cg$115 = $_0_arg.$2;
            if(($cg$115.type === 1)) {
                const $cg$117 = $cg$115.$1;
                if(($cg$117.type === 6)) {
                    
                    if(($cg$115.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$115.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$145 = $_0_arg.$2;
                        
                        if(($cg$145.$2.type === 0)) {
                            const $cg$148 = $_0_arg.$1;
                            if(($cg$148.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$145.$1));
                            } else if(($cg$148.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$145.$1));
                            } else if(($cg$148.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$145.$1));
                            } else if(($cg$148.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$145.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$117.type === 5)) {
                    
                    if(($cg$115.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_($cg$117.$1, 0.0)), $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$139 = $_0_arg.$2;
                        
                        if(($cg$139.$2.type === 0)) {
                            const $cg$142 = $_0_arg.$1;
                            if(($cg$142.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$139.$1));
                            } else if(($cg$142.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$139.$1));
                            } else if(($cg$142.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$139.$1));
                            } else if(($cg$142.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$139.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$117.type === 4)) {
                    
                    if(($cg$115.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_((($cg$117.$1).intValue()), 0.0)), $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$133 = $_0_arg.$2;
                        
                        if(($cg$133.$2.type === 0)) {
                            const $cg$136 = $_0_arg.$1;
                            if(($cg$136.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$133.$1));
                            } else if(($cg$136.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$133.$1));
                            } else if(($cg$136.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$133.$1));
                            } else if(($cg$136.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$133.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$117.type === 7)) {
                    
                    if(($cg$115.$2.type === 0)) {
                        const $cg$130 = Ratio__rationalCast($cg$117.$1);
                        if(($cg$130.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_($cg$130.$1, 0.0)), $HC_0_0$Prelude__List__Nil))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    } else {
                        const $cg$125 = $_0_arg.$2;
                        
                        if(($cg$125.$2.type === 0)) {
                            const $cg$128 = $_0_arg.$1;
                            if(($cg$128.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$125.$1));
                            } else if(($cg$128.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$125.$1));
                            } else if(($cg$128.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$125.$1));
                            } else if(($cg$128.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$125.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else {
                    const $cg$119 = $_0_arg.$2;
                    
                    if(($cg$119.$2.type === 0)) {
                        const $cg$122 = $_0_arg.$1;
                        if(($cg$122.type === 6)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$119.$1));
                        } else if(($cg$122.type === 5)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$119.$1));
                        } else if(($cg$122.type === 4)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$119.$1));
                        } else if(($cg$122.type === 7)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$119.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                    }
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
            }
        } else if(($cg$3.type === 5)) {
            const $cg$80 = $_0_arg.$2;
            if(($cg$80.type === 1)) {
                const $cg$82 = $cg$80.$1;
                if(($cg$82.type === 6)) {
                    
                    if(($cg$80.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_($cg$3.$1, 0.0)), new $HC_2_1$Prelude__List___58__58_($cg$80.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$110 = $_0_arg.$2;
                        
                        if(($cg$110.$2.type === 0)) {
                            const $cg$113 = $_0_arg.$1;
                            if(($cg$113.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$110.$1));
                            } else if(($cg$113.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$110.$1));
                            } else if(($cg$113.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$110.$1));
                            } else if(($cg$113.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$110.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$82.type === 5)) {
                    
                    if(($cg$80.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$80.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$104 = $_0_arg.$2;
                        
                        if(($cg$104.$2.type === 0)) {
                            const $cg$107 = $_0_arg.$1;
                            if(($cg$107.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$104.$1));
                            } else if(($cg$107.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$104.$1));
                            } else if(($cg$107.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$104.$1));
                            } else if(($cg$107.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$104.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$82.type === 4)) {
                    
                    if(($cg$80.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_5$DataTypes__LispFloat((($cg$82.$1).intValue())), $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$98 = $_0_arg.$2;
                        
                        if(($cg$98.$2.type === 0)) {
                            const $cg$101 = $_0_arg.$1;
                            if(($cg$101.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$98.$1));
                            } else if(($cg$101.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$98.$1));
                            } else if(($cg$101.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$98.$1));
                            } else if(($cg$101.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$98.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$82.type === 7)) {
                    
                    if(($cg$80.$2.type === 0)) {
                        const $cg$95 = Ratio__rationalCast($cg$82.$1);
                        if(($cg$95.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_5$DataTypes__LispFloat($cg$95.$1), $HC_0_0$Prelude__List__Nil))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    } else {
                        const $cg$90 = $_0_arg.$2;
                        
                        if(($cg$90.$2.type === 0)) {
                            const $cg$93 = $_0_arg.$1;
                            if(($cg$93.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$90.$1));
                            } else if(($cg$93.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$90.$1));
                            } else if(($cg$93.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$90.$1));
                            } else if(($cg$93.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$90.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else {
                    const $cg$84 = $_0_arg.$2;
                    
                    if(($cg$84.$2.type === 0)) {
                        const $cg$87 = $_0_arg.$1;
                        if(($cg$87.type === 6)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$84.$1));
                        } else if(($cg$87.type === 5)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$84.$1));
                        } else if(($cg$87.type === 4)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$84.$1));
                        } else if(($cg$87.type === 7)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$84.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                    }
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
            }
        } else if(($cg$3.type === 4)) {
            const $cg$47 = $_0_arg.$2;
            if(($cg$47.type === 1)) {
                const $cg$49 = $cg$47.$1;
                if(($cg$49.type === 6)) {
                    
                    if(($cg$47.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_((($cg$3.$1).intValue()), 0.0)), new $HC_2_1$Prelude__List___58__58_($cg$47.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$75 = $_0_arg.$2;
                        
                        if(($cg$75.$2.type === 0)) {
                            const $cg$78 = $_0_arg.$1;
                            if(($cg$78.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$75.$1));
                            } else if(($cg$78.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$75.$1));
                            } else if(($cg$78.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$75.$1));
                            } else if(($cg$78.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$75.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$49.type === 5)) {
                    
                    if(($cg$47.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_5$DataTypes__LispFloat((($cg$3.$1).intValue())), new $HC_2_1$Prelude__List___58__58_($cg$47.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$69 = $_0_arg.$2;
                        
                        if(($cg$69.$2.type === 0)) {
                            const $cg$72 = $_0_arg.$1;
                            if(($cg$72.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$69.$1));
                            } else if(($cg$72.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$69.$1));
                            } else if(($cg$72.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$69.$1));
                            } else if(($cg$72.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$69.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$49.type === 4)) {
                    
                    if(($cg$47.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$47.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$63 = $_0_arg.$2;
                        
                        if(($cg$63.$2.type === 0)) {
                            const $cg$66 = $_0_arg.$1;
                            if(($cg$66.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$63.$1));
                            } else if(($cg$66.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$63.$1));
                            } else if(($cg$66.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$63.$1));
                            } else if(($cg$66.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$63.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$49.type === 7)) {
                    
                    if(($cg$47.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_7$DataTypes__LispRational(new $HC_7_0$Ratio_____37_(new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), $cg$3.$1, (new $JSRTS.jsbn.BigInteger(("1"))))), new $HC_2_1$Prelude__List___58__58_($cg$47.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$57 = $_0_arg.$2;
                        
                        if(($cg$57.$2.type === 0)) {
                            const $cg$60 = $_0_arg.$1;
                            if(($cg$60.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$57.$1));
                            } else if(($cg$60.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$57.$1));
                            } else if(($cg$60.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$57.$1));
                            } else if(($cg$60.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$57.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else {
                    const $cg$51 = $_0_arg.$2;
                    
                    if(($cg$51.$2.type === 0)) {
                        const $cg$54 = $_0_arg.$1;
                        if(($cg$54.type === 6)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$51.$1));
                        } else if(($cg$54.type === 5)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$51.$1));
                        } else if(($cg$54.type === 4)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$51.$1));
                        } else if(($cg$54.type === 7)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$51.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                    }
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
            }
        } else if(($cg$3.type === 7)) {
            const $cg$10 = $_0_arg.$2;
            if(($cg$10.type === 1)) {
                const $cg$12 = $cg$10.$1;
                if(($cg$12.type === 6)) {
                    
                    if(($cg$10.$2.type === 0)) {
                        const $cg$45 = Ratio__rationalCast($cg$3.$1);
                        if(($cg$45.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_($cg$45.$1, 0.0)), new $HC_2_1$Prelude__List___58__58_($cg$10.$1, $HC_0_0$Prelude__List__Nil))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    } else {
                        const $cg$40 = $_0_arg.$2;
                        
                        if(($cg$40.$2.type === 0)) {
                            const $cg$43 = $_0_arg.$1;
                            if(($cg$43.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$40.$1));
                            } else if(($cg$43.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$40.$1));
                            } else if(($cg$43.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$40.$1));
                            } else if(($cg$43.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$40.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$12.type === 5)) {
                    
                    if(($cg$10.$2.type === 0)) {
                        const $cg$37 = Ratio__rationalCast($cg$3.$1);
                        if(($cg$37.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_5$DataTypes__LispFloat($cg$37.$1), new $HC_2_1$Prelude__List___58__58_($cg$10.$1, $HC_0_0$Prelude__List__Nil))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    } else {
                        const $cg$32 = $_0_arg.$2;
                        
                        if(($cg$32.$2.type === 0)) {
                            const $cg$35 = $_0_arg.$1;
                            if(($cg$35.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$32.$1));
                            } else if(($cg$35.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$32.$1));
                            } else if(($cg$35.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$32.$1));
                            } else if(($cg$35.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$32.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$12.type === 4)) {
                    
                    if(($cg$10.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_(new $HC_1_7$DataTypes__LispRational(new $HC_7_0$Ratio_____37_(new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), $cg$12.$1, (new $JSRTS.jsbn.BigInteger(("1"))))), $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$26 = $_0_arg.$2;
                        
                        if(($cg$26.$2.type === 0)) {
                            const $cg$29 = $_0_arg.$1;
                            if(($cg$29.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$26.$1));
                            } else if(($cg$29.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$26.$1));
                            } else if(($cg$29.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$26.$1));
                            } else if(($cg$29.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$26.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else if(($cg$12.type === 7)) {
                    
                    if(($cg$10.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$10.$1, $HC_0_0$Prelude__List__Nil))));
                    } else {
                        const $cg$20 = $_0_arg.$2;
                        
                        if(($cg$20.$2.type === 0)) {
                            const $cg$23 = $_0_arg.$1;
                            if(($cg$23.type === 6)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$20.$1));
                            } else if(($cg$23.type === 5)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$20.$1));
                            } else if(($cg$23.type === 4)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$20.$1));
                            } else if(($cg$23.type === 7)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$20.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                        }
                    }
                } else {
                    const $cg$14 = $_0_arg.$2;
                    
                    if(($cg$14.$2.type === 0)) {
                        const $cg$17 = $_0_arg.$1;
                        if(($cg$17.type === 6)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$14.$1));
                        } else if(($cg$17.type === 5)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$14.$1));
                        } else if(($cg$17.type === 4)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$14.$1));
                        } else if(($cg$17.type === 7)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$14.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                    }
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
            }
        } else {
            const $cg$5 = $_0_arg.$2;
            if(($cg$5.type === 1)) {
                
                if(($cg$5.$2.type === 0)) {
                    const $cg$8 = $_0_arg.$1;
                    if(($cg$8.type === 6)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$5.$1));
                    } else if(($cg$8.type === 5)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$5.$1));
                    } else if(($cg$8.type === 4)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$5.$1));
                    } else if(($cg$8.type === 7)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $cg$5.$1));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Integer", $_0_arg.$1));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in numCast"));
    }
}

// Numbers.numCos

function Numbers__numCos(){
    return $partial_2_3$Numbers__unaryTrig($partial_0_1$Numbers___123_numCos_95_323_125_(), $partial_0_2$Numbers___123_numCos_95_324_125_());
}

// Numbers.numMod

function Numbers__numMod($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$2;
        if(($cg$3.type === 1)) {
            
            if(($cg$3.$2.type === 0)) {
                const $cg$6 = Numbers__numCast(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$3.$1, $HC_0_0$Prelude__List__Nil)));
                if(($cg$6.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left($cg$6.$1);
                } else {
                    return Numbers__numMod_58_doMod_58_0(null, null, $cg$6.$1);
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Numbers.numPrimitives

function Numbers__numPrimitives(){
    return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("+", $partial_0_1$Numbers___123_numPrimitives_95_325_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("-", $partial_0_1$Numbers__numSub()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("*", $partial_0_1$Numbers___123_numPrimitives_95_326_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("/", $partial_0_1$Numbers___123_numPrimitives_95_327_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("modulo", $partial_0_1$Numbers__numMod()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("number?", $partial_0_1$Numbers___123_numPrimitives_95_328_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("complex?", $partial_0_1$Numbers___123_numPrimitives_95_329_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("real?", $partial_0_1$Numbers___123_numPrimitives_95_330_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("rational?", $partial_0_1$Numbers___123_numPrimitives_95_331_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("integer?", $partial_0_1$Numbers__isInteger()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("=", $partial_0_1$Numbers___123_numPrimitives_95_332_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("/=", $partial_0_1$Numbers___123_numPrimitives_95_333_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(">", $partial_0_1$Numbers___123_numPrimitives_95_334_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("<", $partial_0_1$Numbers___123_numPrimitives_95_335_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(">=", $partial_0_1$Numbers___123_numPrimitives_95_336_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("<=", $partial_0_1$Numbers___123_numPrimitives_95_337_125_()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("quotient", $partial_0_1$Numbers__numQuotient()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("remainder", $partial_0_1$Numbers__numRem()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("sin", Numbers__numSine()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("cos", Numbers__numCos()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("number->string", $partial_0_1$Numbers__numToString()), $HC_0_0$Prelude__List__Nil)))))))))))))))))))));
}

// Numbers.numQuotient

function Numbers__numQuotient($_0_arg){
    
    if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0(Prelude__List__length(null, $_0_arg), (new $JSRTS.jsbn.BigInteger(("2"))))) {
        const $cg$3 = Numbers__numCast($_0_arg);
        if(($cg$3.type === 0)) {
            return new $HC_1_0$Prelude__Either__Left($cg$3.$1);
        } else {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 2)) {
                const $cg$7 = $cg$5.$1;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 4)) {
                        const $cg$11 = $cg$7.$2;
                        if(($cg$11.type === 1)) {
                            const $cg$13 = $cg$11.$1;
                            if(($cg$13.type === 4)) {
                                
                                if(($cg$11.$2.type === 0)) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger(Prelude__Interfaces__divBigInt($cg$9.$1, $cg$13.$1)));
                                } else {
                                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
                                }
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Numbers.numRem

function Numbers__numRem($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$2;
        if(($cg$3.type === 1)) {
            
            if(($cg$3.$2.type === 0)) {
                const $cg$6 = Numbers__numCast(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, new $HC_2_1$Prelude__List___58__58_($cg$3.$1, $HC_0_0$Prelude__List__Nil)));
                if(($cg$6.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left($cg$6.$1);
                } else {
                    return Numbers__numRem_58_doRem_58_0(null, null, $cg$6.$1);
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Numbers.numSine

function Numbers__numSine(){
    return $partial_2_3$Numbers__unaryTrig($partial_0_1$Numbers___123_numSine_95_338_125_(), $partial_0_2$Numbers___123_numSine_95_339_125_());
}

// Numbers.numSub

function Numbers__numSub($_0_arg){
    
    if(($_0_arg.type === 1)) {
        
        if(($_0_arg.$2.type === 0)) {
            return Numbers__variadicNumberOp_58_helper_58_0(null, $partial_0_1$Numbers__doSub(), null, new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, $HC_0_0$Prelude__List__Nil), new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(("0")))));
        } else {
            return Numbers__variadicNumberOp_58_helper_58_0(null, $partial_0_1$Numbers__doSub(), null, $_0_arg.$2, $_0_arg.$1);
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.numToInt

function Numbers__numToInt($_0_arg){
    
    if(($_0_arg.type === 6)) {
        const $cg$9 = $_0_arg.$1;
        let $_2_in = null;
        $_2_in = $cg$9.$1;
        const $cg$11 = $_0_arg.$1;
        let $cg$10 = null;
        $cg$10 = $cg$11.$2;
        let $cg$12 = null;
        if((((($cg$10 === 0.0)) ? 1|0 : 0|0) === 0)) {
            $cg$12 = false;
        } else {
            $cg$12 = ($_2_in === ((Util__round($_2_in)).intValue()));
        }
        
        
        if($cg$12) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger(Util__round($_2_in)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Could not convert complex to integer"));
        }
    } else if(($_0_arg.type === 5)) {
        
        if((((($_0_arg.$1 === ((Util__round($_0_arg.$1)).intValue()))) ? 1|0 : 0|0) === 0)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Could not convert float to integer"));
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger(Util__round($_0_arg.$1)));
        }
    } else if(($_0_arg.type === 4)) {
        return new $HC_1_1$Prelude__Either__Right($_0_arg);
    } else if(($_0_arg.type === 7)) {
        const $cg$3 = $_0_arg.$1;
        let $cg$2 = null;
        $cg$2 = $cg$3.$7;
        
        if(((($cg$2.equals((new $JSRTS.jsbn.BigInteger(("1"))))) ? 1|0 : 0|0) === 0)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Could not convert rational to integer"));
        } else {
            const $cg$6 = $_0_arg.$1;
            let $cg$5 = null;
            $cg$5 = $cg$6.$6;
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger($cg$5));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Could not convert non-number to integer"));
    }
}

// Numbers.numToString

function Numbers__numToString($_0_arg){
    
    if(($_0_arg.type === 1)) {
        
        if(($_0_arg.$2.type === 0)) {
            const $cg$4 = $_0_arg.$1;
            let $cg$3 = null;
            if(($cg$4.type === 6)) {
                $cg$3 = new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else if(($cg$4.type === 5)) {
                $cg$3 = new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else if(($cg$4.type === 7)) {
                $cg$3 = new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                $cg$3 = Numbers__isInteger(new $HC_2_1$Prelude__List___58__58_($_0_arg.$1, $HC_0_0$Prelude__List__Nil));
            }
            
            
            if(($cg$3.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left($cg$3.$1);
            } else {
                const $cg$7 = $cg$3.$1;
                if(($cg$7.type === 10)) {
                    const $cg$9 = $cg$7.$1;
                    if((!$cg$9)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("number?", $_0_arg.$1));
                    } else if($cg$9) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_8$DataTypes__LispString(DataTypes__showVal($_0_arg.$1)));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error"));
                }
            }
        } else {
            return new $JSRTS.Lazy((function(){
                return (function(){
                    return Numbers___123_numToString_95_340_125_();
                })();
            }));
        }
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Numbers___123_numToString_95_340_125_();
            })();
        }));
    }
}

// ParseNumber.octConverter

function ParseNumber__octConverter($_0_arg){
    
    if(($_0_arg === "0")) {
        return (new $JSRTS.jsbn.BigInteger(("0")));
    } else if(($_0_arg === "1")) {
        return (new $JSRTS.jsbn.BigInteger(("1")));
    } else if(($_0_arg === "2")) {
        return (new $JSRTS.jsbn.BigInteger(("2")));
    } else if(($_0_arg === "3")) {
        return (new $JSRTS.jsbn.BigInteger(("3")));
    } else if(($_0_arg === "4")) {
        return (new $JSRTS.jsbn.BigInteger(("4")));
    } else if(($_0_arg === "5")) {
        return (new $JSRTS.jsbn.BigInteger(("5")));
    } else if(($_0_arg === "6")) {
        return (new $JSRTS.jsbn.BigInteger(("6")));
    } else if(($_0_arg === "7")) {
        return (new $JSRTS.jsbn.BigInteger(("7")));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_octConverter_95_342_125_();
            })();
        }));
    }
}

// ParserCombinator.oneOf

function ParserCombinator__oneOf($_0_arg){
    
    if(($_0_arg === "")) {
        return $partial_2_3$ParserCombinator__failure(null, "Empty input to \'OneOf\'");
    } else {
        let $cg$2 = null;
        if(($_0_arg === "")) {
            $cg$2 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the tail of an empty string"));
        } else {
            $cg$2 = $_0_arg.slice(1);
        }
        
        return $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_1_2$ParserCombinator___123_oneOf_95_343_125_($_0_arg)), ParserCombinator__oneOf($cg$2));
    }
}

// Bools.or

function Bools__or($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
            } else {
                const $cg$4 = $_0_arg.$1;
                if(($cg$4.type === 10)) {
                    
                    if($cg$4.$1) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                    } else {
                        $_0_arg = $_0_arg.$2;
                    }
                } else {
                    return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
                }
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    }
}

// Vector.outOfBoundsError

function Vector__outOfBoundsError($_0_arg, $_1_arg, $_2_arg){
    return new $HC_1_6$DataTypes__Default(($_0_arg + (": index is out of range; " + ("index: " + (Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $_1_arg) + ("; valid range: " + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, Prelude__List__length(null, $_2_arg))))))));
}

// Parse.parseAtom

function Parse__parseAtom(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Parse___123_parseAtom_95_344_125_()), ParserCombinator__oneOf("!#$%&|*+-/:<=>?@^_~")), $partial_0_1$Parse___123_parseAtom_95_348_125_());
}

// Parse.parseBlockComment

function Parse__parseBlockComment(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__string("#|"), $partial_0_1$Parse___123_parseBlockComment_95_350_125_());
}

// Parse.parseCharacter

function Parse__parseCharacter(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__string("#\\"), $partial_0_1$Parse___123_parseCharacter_95_356_125_());
}

// ParseNumber.parseComplexBase

function ParseNumber__parseComplexBase($_0_arg){
    
    if(($_0_arg === "b")) {
        return ParseNumber__parseComplexBinary();
    } else if(($_0_arg === "d")) {
        return ParseNumber__parseComplexDecimal();
    } else if(($_0_arg === "o")) {
        return ParseNumber__parseComplexOctal();
    } else if(($_0_arg === "x")) {
        return ParseNumber__parseComplexHex();
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Bad complex format");
    }
}

// ParseNumber.parseComplexBinary

function ParseNumber__parseComplexBinary(){
    return ParseNumber__parseComplexHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01")), ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01"), (new $JSRTS.jsbn.BigInteger(("2")))), ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01"))));
}

// ParseNumber.parseComplexDecimal

function ParseNumber__parseComplexDecimal(){
    return ParseNumber__parseComplexHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit())), ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), (new $JSRTS.jsbn.BigInteger(("10")))), ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()))));
}

// ParseNumber.parseComplexHelper

function ParseNumber__parseComplexHelper($_0_arg, $_1_arg, $_2_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(null, null, $partial_0_1$ParseNumber___123_parseComplexHelper_95_364_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, $_2_arg, $partial_3_4$ParserCombinator___60__124__62_(null, $_1_arg, $_0_arg))), $partial_3_4$ParseNumber___123_parseComplexHelper_95_371_125_($_2_arg, $_1_arg, $_0_arg));
}

// ParseNumber.parseComplexHex

function ParseNumber__parseComplexHex(){
    return ParseNumber__parseComplexHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef"))), ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef")), (new $JSRTS.jsbn.BigInteger(("16")))), ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef")))));
}

// ParseNumber.parseComplexOctal

function ParseNumber__parseComplexOctal(){
    return ParseNumber__parseComplexHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit())), ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__oneOf("01234567"), (new $JSRTS.jsbn.BigInteger(("8")))), ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()))));
}

// Parse.parseDottedList

function Parse__parseDottedList(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseDottedList_95_386_125_());
}

// Parse.parseExpr

function Parse__parseExpr(){
    return $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseVector(), $partial_3_4$ParserCombinator___60__124__62_(null, $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseLineComment(), Parse__parseBlockComment()), $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseNumber(), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseCharacter(), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseAtom(), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseString(), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseQuoted(), Parse__bracketed(null, $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseTwoDot(), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseDottedList(), Parse__parseList()))))))))));
}

// ParseNumber.parseFloat

function ParseNumber__parseFloat(){
    return $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), (new $JSRTS.jsbn.BigInteger(("10")))), $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloat_95_388_125_()), $partial_0_1$ParseNumber___123_parseFloat_95_389_125_()));
}

// ParseNumber.parseFloatBase

function ParseNumber__parseFloatBase($_0_arg){
    
    if(($_0_arg === "b")) {
        return ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01"), (new $JSRTS.jsbn.BigInteger(("2"))));
    } else if(($_0_arg === "d")) {
        return ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), (new $JSRTS.jsbn.BigInteger(("10"))));
    } else if(($_0_arg === "o")) {
        return ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__oneOf("01234567"), (new $JSRTS.jsbn.BigInteger(("8"))));
    } else if(($_0_arg === "x")) {
        return ParseNumber__parseFloatHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef")), (new $JSRTS.jsbn.BigInteger(("16"))));
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Bad float format");
    }
}

// ParseNumber.parseFloatHelper

function ParseNumber__parseFloatHelper($_0_arg, $_1_arg, $_2_arg){
    return $partial_3_4$ParserCombinator___60__124__62_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloatHelper_95_394_125_()), $partial_3_4$ParseNumber___123_parseFloatHelper_95_396_125_($_0_arg, $_1_arg, $_2_arg)), $partial_3_4$ParserCombinator___60__124__62_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloatHelper_95_397_125_()), $partial_3_4$ParseNumber___123_parseFloatHelper_95_399_125_($_0_arg, $_1_arg, $_2_arg)), ParseNumber__parseFloatHelper_58_parseFloat_39__58_0($_0_arg, $_1_arg, $_2_arg, $partial_0_1$Lists___123_cons_95_14_125_())));
}

// ParseNumber.parseInteger

function ParseNumber__parseInteger(){
    return $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit())), $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloat_95_388_125_()), $partial_0_1$ParseNumber___123_parseInteger_95_403_125_()));
}

// ParseNumber.parseIntegerBase

function ParseNumber__parseIntegerBase($_0_arg){
    
    if(($_0_arg === "b")) {
        return ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01"));
    } else if(($_0_arg === "d")) {
        return ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()));
    } else if(($_0_arg === "o")) {
        return ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()));
    } else if(($_0_arg === "x")) {
        return ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef")));
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Bad integer format");
    }
}

// ParseNumber.parseIntegerHelper

function ParseNumber__parseIntegerHelper($_0_arg, $_1_arg){
    return $partial_3_4$ParserCombinator___60__124__62_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloatHelper_95_394_125_()), $partial_2_3$ParseNumber___123_parseIntegerHelper_95_410_125_($_0_arg, $_1_arg)), $partial_3_4$ParserCombinator___60__124__62_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloatHelper_95_397_125_()), $partial_2_3$ParseNumber___123_parseIntegerHelper_95_413_125_($_0_arg, $_1_arg)), ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0($_0_arg, $_1_arg, $partial_0_1$Lists___123_cons_95_14_125_())));
}

// Parse.parseLineComment

function Parse__parseLineComment(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseLineComment_95_415_125_()), $partial_0_1$Parse___123_parseLineComment_95_418_125_());
}

// Parse.parseList

function Parse__parseList(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__parseRawList(), $partial_0_2$Parse___123_parseList_95_419_125_());
}

// ParseNumber.parseNumber

function ParseNumber__parseNumber(){
    return $partial_3_4$ParserCombinator___60__124__62_(null, $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseComplexDecimal(), $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloat_95_388_125_()), $partial_0_1$ParseNumber___123_parseNumber_95_421_125_())), $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseRational(), $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseFloat(), ParseNumber__parseInteger())));
}

// Parse.parseQuoted

function Parse__parseQuoted(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseQuoted_95_422_125_()), $partial_0_1$Parse___123_parseQuoted_95_424_125_());
}

// ParseNumber.parseRational

function ParseNumber__parseRational(){
    return $partial_3_4$ParserCombinator___60__124__62_(null, ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()))), $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloat_95_388_125_()), $partial_0_1$ParseNumber___123_parseRational_95_427_125_()));
}

// ParseNumber.parseRationalBase

function ParseNumber__parseRationalBase($_0_arg){
    
    if(($_0_arg === "b")) {
        return ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexBinary_95_357_125_(), ParserCombinator__oneOf("01")));
    } else if(($_0_arg === "d")) {
        return ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexDecimal_95_360_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit())));
    } else if(($_0_arg === "o")) {
        return ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexOctal_95_375_125_(), ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit())));
    } else if(($_0_arg === "x")) {
        return ParseNumber__parseRationalHelper(ParseNumber__parseIntegerHelper($partial_0_1$ParseNumber___123_parseComplexHex_95_372_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("ABCDEFabcdef"))));
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Bad rational format");
    }
}

// ParseNumber.parseRationalHelper

function ParseNumber__parseRationalHelper($_0_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(null, null, $partial_0_1$ParseNumber___123_parseRationalHelper_95_433_125_(), $_0_arg), $partial_1_2$ParseNumber___123_parseRationalHelper_95_457_125_($_0_arg));
}

// Parse.parseRawList

function Parse__parseRawList(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseRawList_95_460_125_());
}

// Parse.parseString

function Parse__parseString(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseString_95_461_125_()), $partial_0_1$Parse___123_parseString_95_466_125_());
}

// Parse.parseTwoDot

function Parse__parseTwoDot(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseTwoDot_95_479_125_());
}

// Parse.parseVector

function Parse__parseVector(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseFloat_95_388_125_()), $partial_0_1$Parse___123_parseVector_95_482_125_());
}

// Prelude.pow

function Prelude__pow($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if($_3_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        
        return $_1_arg.$3((new $JSRTS.jsbn.BigInteger(("1"))));
    } else {
        const $_7_in = $_3_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        
        return $_1_arg.$2($_2_arg)(Prelude__pow(null, $_1_arg, $_2_arg, $_7_in));
    }
}

// Prelude.Show.primNumShow

function Prelude__Show__primNumShow($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    const $_4_in = $_1_arg($_3_arg);
    let $cg$1 = null;
    if(($_2_arg.type === 0)) {
        $cg$1 = (new $JSRTS.jsbn.BigInteger(("0")));
    } else {
        $cg$1 = (new $JSRTS.jsbn.BigInteger(("4")));
    }
    
    let $cg$2 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($cg$1, (new $JSRTS.jsbn.BigInteger(("5")))) > 0)) {
        $cg$2 = true;
    } else {
        let $cg$3 = null;
        if(($_2_arg.type === 0)) {
            $cg$3 = (new $JSRTS.jsbn.BigInteger(("0")));
        } else {
            $cg$3 = (new $JSRTS.jsbn.BigInteger(("4")));
        }
        
        $cg$2 = $cg$3.equals((new $JSRTS.jsbn.BigInteger(("5"))));
    }
    
    let $cg$4 = null;
    if($cg$2) {
        let $cg$5 = null;
        if((((($_4_in == "")) ? 1|0 : 0|0) === 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = false;
        }
        
        
        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$5, true).type === 1)) {
            $cg$4 = false;
        } else {
            $cg$4 = ($_4_in[0] === "-");
        }
    } else {
        $cg$4 = false;
    }
    
    
    if($cg$4) {
        return ("(" + ($_4_in + ")"));
    } else {
        return $_4_in;
    }
}

// Eval.primitiveBindings

function Eval__primitiveBindings($_0_arg, $_1_arg){
    
    const $cg$3 = $_1_arg.$3;
    return $cg$3.$2(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Eval___123_primitiveBindings_95_483_125_(), Primitives__primitives()));
}

// Primitives.primitives

function Primitives__primitives(){
    return Prelude__List___43__43_(null, Vector__vectorPrimitives(), Prelude__List___43__43_(null, Lists__listPrimitives(), Prelude__List___43__43_(null, Numbers__numPrimitives(), Prelude__List___43__43_(null, Strings__strPrimitives(), Prelude__List___43__43_(null, Bools__boolPrimitives(), Prelude__List___43__43_(null, Symbols__symbolPrimitives(), Prelude__List___43__43_(null, new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("procedure?", $partial_0_1$Procedures__isProcedure()), $HC_0_0$Prelude__List__Nil), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("char?", $partial_0_1$Primitives__isChar()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("eq?", $partial_0_1$Primitives__eqv()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("eqv?", $partial_0_1$Primitives__eqv()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("equal?", $partial_0_1$Primitives__eqv()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("void", $partial_0_1$Primitives___123_primitives_95_484_125_()), $HC_0_0$Prelude__List__Nil))))))))))));
}

// Prelude.Show.protectEsc

function Prelude__Show__protectEsc($_0_arg, $_1_arg, $_2_arg){
    let $cg$1 = null;
    if((((($_2_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    let $cg$2 = null;
    if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true).type === 1)) {
        $cg$2 = false;
    } else {
        $cg$2 = $_0_arg($_2_arg[0]);
    }
    
    let $cg$3 = null;
    if($cg$2) {
        $cg$3 = "\\&";
    } else {
        $cg$3 = "";
    }
    
    return ($_1_arg + ($cg$3 + $_2_arg));
}

// Ratio.rationalAdd

function Ratio__rationalAdd($_0_arg, $_1_arg, $_2_arg){
    
    
    const $cg$4 = $_2_arg.$1;
    let $cg$3 = null;
    const $cg$6 = $cg$4.$1;
    const $cg$8 = $_2_arg.$1;
    let $cg$7 = null;
    const $cg$10 = $cg$8.$1;
    $cg$7 = $cg$10.$2($_1_arg.$6)($_2_arg.$7);
    const $cg$12 = $_2_arg.$1;
    let $cg$11 = null;
    const $cg$14 = $cg$12.$1;
    $cg$11 = $cg$14.$2($_1_arg.$7)($_2_arg.$6);
    $cg$3 = $cg$6.$1($cg$7)($cg$11);
    const $cg$16 = $_2_arg.$1;
    let $cg$15 = null;
    const $cg$18 = $cg$16.$1;
    $cg$15 = $cg$18.$2($_1_arg.$7)($_2_arg.$7);
    return Ratio___58__37_(null, $_2_arg.$1, $_2_arg.$2, $_2_arg.$3, $_2_arg.$4, $_2_arg.$5, $cg$3, $cg$15);
}

// Numbers.rationalBinaryOpHelper

function Numbers__rationalBinaryOpHelper($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    const $cg$2 = $_0_arg($_1_arg)($_2_arg);
    if(($cg$2.type === 1)) {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_7$DataTypes__LispRational($cg$2.$1));
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(("Unexpected error in " + $_3_arg)));
    }
}

// Ratio.rationalCast

function Ratio__rationalCast($_0_arg){
    
    
    if(((($_0_arg.$7.equals((new $JSRTS.jsbn.BigInteger(("0"))))) ? 1|0 : 0|0) === 0)) {
        return new $HC_1_1$Prelude__Maybe__Just(((($_0_arg.$6).intValue()) / (($_0_arg.$7).intValue())));
    } else {
        return $HC_0_0$Prelude__Maybe__Nothing;
    }
}

// Ratio.rationalDiv

function Ratio__rationalDiv($_0_arg, $_1_arg, $_2_arg){
    
    
    const $cg$4 = $_2_arg.$1;
    let $cg$3 = null;
    const $cg$6 = $cg$4.$1;
    $cg$3 = $cg$6.$2($_1_arg.$6)($_2_arg.$7);
    const $cg$8 = $_2_arg.$1;
    let $cg$7 = null;
    const $cg$10 = $cg$8.$1;
    $cg$7 = $cg$10.$2($_1_arg.$7)($_2_arg.$6);
    return Ratio___58__37_(null, $_2_arg.$1, $_2_arg.$2, $_2_arg.$3, $_2_arg.$4, $_2_arg.$5, $cg$3, $cg$7);
}

// Ratio.rationalMul

function Ratio__rationalMul($_0_arg, $_1_arg, $_2_arg){
    
    
    const $cg$4 = $_2_arg.$1;
    let $cg$3 = null;
    const $cg$6 = $cg$4.$1;
    $cg$3 = $cg$6.$2($_1_arg.$6)($_2_arg.$6);
    const $cg$8 = $_2_arg.$1;
    let $cg$7 = null;
    const $cg$10 = $cg$8.$1;
    $cg$7 = $cg$10.$2($_1_arg.$7)($_2_arg.$7);
    return Ratio___58__37_(null, $_2_arg.$1, $_2_arg.$2, $_2_arg.$3, $_2_arg.$4, $_2_arg.$5, $cg$3, $cg$7);
}

// Ratio.rationalSub

function Ratio__rationalSub($_0_arg, $_1_arg, $_2_arg){
    
    
    const $cg$4 = $_2_arg.$5;
    let $cg$3 = null;
    const $cg$6 = $_2_arg.$1;
    let $cg$5 = null;
    const $cg$8 = $cg$6.$1;
    $cg$5 = $cg$8.$2($_1_arg.$6)($_2_arg.$7);
    const $cg$10 = $_2_arg.$1;
    let $cg$9 = null;
    const $cg$12 = $cg$10.$1;
    $cg$9 = $cg$12.$2($_2_arg.$6)($_1_arg.$7);
    $cg$3 = $cg$4.$2($cg$5)($cg$9);
    const $cg$14 = $_2_arg.$1;
    let $cg$13 = null;
    const $cg$16 = $cg$14.$1;
    $cg$13 = $cg$16.$2($_1_arg.$7)($_2_arg.$7);
    return Ratio___58__37_(null, $_2_arg.$1, $_2_arg.$2, $_2_arg.$3, $_2_arg.$4, $_2_arg.$5, $cg$3, $cg$13);
}

// Repl.readExprList

function Repl__readExprList($_0_arg, $_1_arg){
    return $partial_4_5$Repl__readOrThrow(null, null, $_1_arg, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())), $partial_0_1$Repl___123_readExprList_95_485_125_()));
}

// Repl.readOrThrow

function Repl__readOrThrow($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    const $cg$2 = $_3_arg($_4_arg);
    if(($cg$2.type === 0)) {
        const $cg$12 = $cg$2.$1;
        
        return $_2_arg.$1(null)(null)(new $HC_1_5$DataTypes__ParseError($cg$12.$1));
    } else if(($cg$2.type === 1)) {
        const $cg$5 = $cg$2.$1;
        if(($cg$5.type === 1)) {
            const $cg$8 = $cg$5.$1;
            
            if(($cg$5.$2.type === 0)) {
                return new $HC_1_0$Control__ST__Pure($cg$8.$1);
            } else {
                
                return $_2_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Read error"));
            }
        } else {
            
            return $_2_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Read error"));
        }
    } else {
        
        return $_2_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("Read error"));
    }
}

// Control.ST.rebuildEnv

function Control__ST__rebuildEnv($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    return $_3_arg;
}

// ParserCombinator.rej

function ParserCombinator__rej($_0_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_0_1$ParserCombinator__item(), $partial_1_2$ParserCombinator___123_rej_95_487_125_($_0_arg));
}

// Main.replEval

function Main__replEval($_0_arg){
    return $partial_7_8$Control__IOExcept__ioe_95_run(null, null, null, null, Control__ST__runST(null, null, null, null, null, $HC_0_0$Control__ST__Env__Nil, new $HC_2_1$Control__ST__Bind(Eval__primitiveBindings(null, new $HC_3_0$DataTypes__Context_95_ictor($partial_0_3$Main___123_replEval_95_488_125_(), $partial_0_2$Main___123_replEval_95_489_125_(), new $HC_6_0$Environment__Envir_95_ictor($partial_0_2$Main___123_replEval_95_493_125_(), $partial_0_1$Main___123_replEval_95_497_125_(), $partial_0_2$Main___123_replEval_95_501_125_(), $partial_0_3$Main___123_replEval_95_505_125_(), $partial_0_3$Main___123_replEval_95_509_125_(), $partial_0_2$Main___123_replEval_95_513_125_()))), $partial_1_2$Main___123_replEval_95_542_125_($_0_arg)), $partial_0_3$Main___123_replEval_95_543_125_()), $partial_0_2$Main___123_replEval_95_544_125_(), $partial_0_2$Main___123_replEval_95_545_125_());
}

// Prelude.List.replicate

function Prelude__List__replicate($_0_arg, $_1_arg, $_2_arg){
    
    if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
        return new $HC_2_1$Prelude__List___58__58_($_2_arg, Prelude__List__replicate(null, $_3_in, $_2_arg));
    }
}

// Prelude.List.reverseOnto

function Prelude__List__reverseOnto($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, $_1_arg);
            $_2_arg = $_2_arg.$2;
        } else {
            return $_1_arg;
        }
    }
}

// Util.round

function Util__round($_0_arg){
    let $_1_in = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_0_arg, 0.0) > 0)) {
        $_1_in = ($_0_arg - Math.floor($_0_arg));
    } else {
        $_1_in = (-(($_0_arg - Math.ceil($_0_arg))));
    }
    
    let $cg$2 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_0_arg, 0.0) > 0)) {
        $cg$2 = (new $JSRTS.jsbn.BigInteger(("1")));
    } else {
        
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_0_arg, 0.0) < 0)) {
            $cg$2 = (new $JSRTS.jsbn.BigInteger(("-1")));
        } else {
            $cg$2 = (new $JSRTS.jsbn.BigInteger(("0")));
        }
    }
    
    let $cg$4 = null;
    if(((($cg$2.equals((new $JSRTS.jsbn.BigInteger(("1"))))) ? 1|0 : 0|0) === 0)) {
        let $cg$5 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_1_in, 0.5) < 0)) {
            $cg$5 = true;
        } else {
            $cg$5 = ($_1_in === 0.5);
        }
        
        
        if($cg$5) {
            $cg$4 = Math.ceil($_0_arg);
        } else {
            $cg$4 = Math.floor($_0_arg);
        }
    } else {
        let $cg$7 = null;
        if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_1_in, 0.5) < 0)) {
            $cg$7 = true;
        } else {
            $cg$7 = ($_1_in === 0.5);
        }
        
        
        if($cg$7) {
            $cg$4 = Math.floor($_0_arg);
        } else {
            $cg$4 = Math.ceil($_0_arg);
        }
    }
    
    return (new $JSRTS.jsbn.BigInteger(Math.trunc(($cg$4))+ ''));
}

// Main.run

function Main__run($_0_arg, $_1_in){
    const $_2_in = Main__replEval($_0_arg)($_1_in);
    return $_2_in;
}

// Control.ST.runST

function Control__ST__runST($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    let $tco$$_7_arg = $_7_arg;
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $tco$$_7_arg = $partial_2_4$Control__ST___123_runST_95_546_125_($_6_arg.$2, $_7_arg);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = $_5_arg;
            $_6_arg = $_6_arg.$1;
            $_7_arg = $tco$$_7_arg;
        } else if(($_6_arg.type === 10)) {
            $tco$$_7_arg = $partial_3_5$Control__ST___123_runST_95_547_125_($_7_arg, $_5_arg, $_6_arg.$2);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = Control__ST__dropEnv(null, null, $_5_arg, $_6_arg.$2);
            $_6_arg = $_6_arg.$1;
            $_7_arg = $tco$$_7_arg;
        } else if(($_6_arg.type === 2)) {
            return $_6_arg.$1(null)(null)($_6_arg.$2)($partial_2_3$Control__ST___123_runST_95_548_125_($_7_arg, $_5_arg));
        } else {
            return $_7_arg($_6_arg.$1)($_5_arg);
        }
    }
}

// ParserCombinator.sat

function ParserCombinator__sat($_0_arg){
    return $partial_2_3$ParserCombinator__try(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_0_1$ParserCombinator__item(), $partial_1_2$ParserCombinator___123_sat_95_551_125_($_0_arg)));
}

// ParserCombinator.sepBy

function ParserCombinator__sepBy($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sepBy_58_separated_58_0(null, null, $_2_arg, $_3_arg), $partial_0_1$ParserCombinator___123_many_39__95_277_125_());
}

// DataTypes.showError

function DataTypes__showError($_0_arg){
    
    if(($_0_arg.type === 2)) {
        return ($_0_arg.$1 + (": " + DataTypes__showVal($_0_arg.$2)));
    } else if(($_0_arg.type === 6)) {
        return $_0_arg.$1;
    } else if(($_0_arg.type === 0)) {
        const $cg$7 = $_0_arg.$1;
        let $_11_in = null;
        if(($cg$7.type === 0)) {
            $_11_in = ("arity mismatch;\nthe expected number of arguments does not match the given number" + ("\nexpected: at least " + (Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrInt(), $HC_0_0$Prelude__Show__Open, $cg$7.$1) + ("\ngiven: " + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $_0_arg.$2)))));
        } else {
            let $cg$8 = null;
            if((((($cg$7.$1 === $cg$7.$2)) ? 1|0 : 0|0) === 0)) {
                $cg$8 = ("between " + (Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrInt(), $HC_0_0$Prelude__Show__Open, $cg$7.$1) + (" and " + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrInt(), $HC_0_0$Prelude__Show__Open, $cg$7.$2))));
            } else {
                $cg$8 = Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrInt(), $HC_0_0$Prelude__Show__Open, $cg$7.$1);
            }
            
            $_11_in = ("arity mismatch;\nthe expected number of arguments does not match the given number" + ("\nexpected: " + ($cg$8 + ("\ngiven: " + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $_0_arg.$2)))));
        }
        
        let $cg$9 = null;
        if(($_0_arg.$3.type === 0)) {
            $cg$9 = "";
        } else {
            $cg$9 = ("\narguments:\n" + Prelude__Strings__unwords(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $_0_arg.$3)));
        }
        
        return ($_11_in + $cg$9);
    } else if(($_0_arg.type === 5)) {
        let $cg$2 = null;
        if((((($_0_arg.$1 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        let $cg$3 = null;
        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true).type === 1)) {
            $cg$3 = $HC_0_0$Prelude__List__Nil;
        } else {
            let $cg$4 = null;
            if((((($_0_arg.$1.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                $cg$4 = true;
            } else {
                $cg$4 = false;
            }
            
            let $cg$5 = null;
            if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$4, true).type === 1)) {
                $cg$5 = $HC_0_0$Prelude__Strings__StrNil;
            } else {
                $cg$5 = new $HC_2_1$Prelude__Strings__StrCons($_0_arg.$1.slice(1)[0], $_0_arg.$1.slice(1).slice(1));
            }
            
            $cg$3 = new $HC_2_1$Prelude__List___58__58_($_0_arg.$1[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$5));
        }
        
        return ("Parse error at " + (("\"")+(Prelude__Show__showLitString($cg$3, "\""))));
    } else {
        return ("Invalid type: expected " + ($_0_arg.$1 + (", found " + DataTypes__showVal($_0_arg.$2))));
    }
}

// Prelude.Show.showLitChar

function Prelude__Show__showLitChar($_0_arg){
    
    if(($_0_arg === "\x07")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_553_125_();
    } else if(($_0_arg === "\b")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_554_125_();
    } else if(($_0_arg === "\t")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_555_125_();
    } else if(($_0_arg === "\n")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_556_125_();
    } else if(($_0_arg === "\v")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_557_125_();
    } else if(($_0_arg === "\f")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_558_125_();
    } else if(($_0_arg === "\r")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_559_125_();
    } else if(($_0_arg === "\x0e")) {
        return $partial_2_3$Prelude__Show__protectEsc($partial_0_1$Prelude__Show___123_showLitChar_95_560_125_(), "\\SO");
    } else if(($_0_arg === "\\")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_561_125_();
    } else if(($_0_arg === "\x7f")) {
        return $partial_0_1$Prelude__Show___123_showLitChar_95_562_125_();
    } else {
        const $cg$3 = Prelude__Show__showLitChar_58_getAt_58_10(null, (new $JSRTS.jsbn.BigInteger(''+((($_0_arg).charCodeAt(0)|0)))), Prelude__Show__showLitChar_58_asciiTab_58_10(null));
        if(($cg$3.type === 1)) {
            return $partial_1_2$Prelude__Show___123_showLitChar_95_563_125_($cg$3.$1);
        } else {
            
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, "\x7f") > 0)) {
                return $partial_1_2$Prelude__Show___123_showLitChar_95_564_125_($_0_arg);
            } else {
                return $partial_1_2$prim_95__95_strCons($_0_arg);
            }
        }
    }
}

// Prelude.Show.showLitString

function Prelude__Show__showLitString($_0_arg, $_4_in){
    
    if(($_0_arg.type === 1)) {
        
        if(($_0_arg.$1 === "\"")) {
            return ("\\\"" + Prelude__Show__showLitString($_0_arg.$2, $_4_in));
        } else {
            return Prelude__Show__showLitChar($_0_arg.$1)(Prelude__Show__showLitString($_0_arg.$2, $_4_in));
        }
    } else {
        return $_4_in;
    }
}

// DataTypes.showVal

function DataTypes__showVal($_0_arg){
    
    if(($_0_arg.type === 1)) {
        return $_0_arg.$1;
    } else if(($_0_arg.type === 10)) {
        const $cg$5 = $_0_arg.$1;
        if((!$cg$5)) {
            return "#f";
        } else if($cg$5) {
            return "#t";
        } else {
            return "";
        }
    } else if(($_0_arg.type === 6)) {
        return Prelude__Show__Data__Complex___64_Prelude__Show__Show_36_Complex_32_a_58__33_showPrec_58_0(null, new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes___123_showVal_95_565_125_(), $partial_0_2$DataTypes___123_showVal_95_566_125_()), $HC_0_0$Prelude__Show__Open, $_0_arg.$1);
    } else if(($_0_arg.type === 3)) {
        return ("(" + (Prelude__Strings__unwords(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $_0_arg.$1)) + (" . " + (DataTypes__showVal($JSRTS.force($_0_arg.$2)) + ")"))));
    } else if(($_0_arg.type === 5)) {
        return Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_floatToStr(), $HC_0_0$Prelude__Show__Open, $_0_arg.$1);
    } else if(($_0_arg.type === 12)) {
        return ("#<procedure:" + ($_0_arg.$1 + ">"));
    } else if(($_0_arg.type === 4)) {
        return Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $_0_arg.$1);
    } else if(($_0_arg.type === 2)) {
        return ("(" + (Prelude__Strings__unwords(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $_0_arg.$1)) + ")"));
    } else if(($_0_arg.type === 7)) {
        const $cg$3 = $_0_arg.$1;
        return (Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $cg$3.$6) + ("/" + Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrBigInt(), $HC_0_0$Prelude__Show__Open, $cg$3.$7)));
    } else if(($_0_arg.type === 8)) {
        return ("\"" + ($_0_arg.$1 + "\""));
    } else if(($_0_arg.type === 0)) {
        return ("#(" + (Prelude__Strings__unwords(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $_0_arg.$2)) + ")"));
    } else if(($_0_arg.type === 13)) {
        return "";
    } else {
        return "";
    }
}

// ParserCombinator.skipMany

function ParserCombinator__skipMany($_0_arg, $_1_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many_39_(null, $_1_arg), $partial_0_2$ParserCombinator___123_skipMany_95_567_125_());
}

// ParserCombinator.skipMany1

function ParserCombinator__skipMany1($_0_arg, $_1_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many1(null, $_1_arg), $partial_0_2$ParserCombinator___123_skipMany_95_567_125_());
}

// Strings.strAppend

function Strings__strAppend($_0_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            const $cg$3 = $_0_arg.$1;
            if(($cg$3.type === 8)) {
                const $cg$5 = $_0_arg.$2;
                if(($cg$5.type === 1)) {
                    const $cg$7 = $cg$5.$1;
                    if(($cg$7.type === 8)) {
                        $_0_arg = new $HC_2_1$Prelude__List___58__58_(new $HC_1_8$DataTypes__LispString(($cg$3.$1 + $cg$7.$1)), $cg$5.$2);
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-append`"));
                    }
                } else if(($cg$5.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-append`"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-append`"));
            }
        } else if(($_0_arg.type === 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_8$DataTypes__LispString(""));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-append`"));
        }
    }
}

// Strings.strLen

function Strings__strLen($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 8)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(''+((($cg$3.$1).length))))));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-length`"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-length`"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Invalid arguments to `string-length`"));
    }
}

// Strings.strPrimitives

function Strings__strPrimitives(){
    return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string=?", $partial_3_4$Util__boolBinop(null, $partial_0_1$Strings__unpackStr(), $partial_0_2$Util___123_initEnv_39__95_273_125_())), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string<?", $partial_3_4$Util__boolBinop(null, $partial_0_1$Strings__unpackStr(), $partial_0_2$Strings___123_strPrimitives_95_570_125_())), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string>?", $partial_3_4$Util__boolBinop(null, $partial_0_1$Strings__unpackStr(), $partial_0_2$Strings___123_strPrimitives_95_571_125_())), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string<=?", $partial_3_4$Util__boolBinop(null, $partial_0_1$Strings__unpackStr(), $partial_0_2$Util___123_initEnv_39__95_275_125_())), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string>=?", $partial_3_4$Util__boolBinop(null, $partial_0_1$Strings__unpackStr(), $partial_0_2$Strings___123_strPrimitives_95_573_125_())), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string?", $partial_0_1$Strings__isString()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string->symbol", $partial_0_1$Strings__stringToSymbol()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string-ref", $partial_0_1$Strings__stringRef()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("make-string", $partial_0_1$Strings__makeString()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string-length", $partial_0_1$Strings__strLen()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("string-append", $partial_0_1$Strings__strAppend()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("substring", $partial_0_1$Strings__substring()), $HC_0_0$Prelude__List__Nil))))))))))));
}

// ParserCombinator.string

function ParserCombinator__string($_0_arg){
    
    if(($_0_arg === "")) {
        return $partial_0_1$ParserCombinator___123_string_95_574_125_();
    } else {
        return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_1_2$ParserCombinator___123_oneOf_95_343_125_($_0_arg)), $partial_1_2$ParserCombinator___123_string_95_577_125_($_0_arg));
    }
}

// Strings.stringRef

function Strings__stringRef($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 8)) {
            const $cg$25 = $_0_arg.$2;
            if(($cg$25.type === 1)) {
                const $cg$27 = $cg$25.$1;
                if(($cg$27.type === 4)) {
                    
                    if(($cg$25.$2.type === 0)) {
                        const $_7_in = $cg$27.$1;
                        let $cg$51 = null;
                        if((((($cg$3.$1 == "")) ? 1|0 : 0|0) === 0)) {
                            $cg$51 = true;
                        } else {
                            $cg$51 = false;
                        }
                        
                        let $cg$52 = null;
                        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$51, true).type === 1)) {
                            $cg$52 = $HC_0_0$Prelude__Maybe__Nothing;
                        } else {
                            
                            if($_7_in.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                                $cg$52 = new $HC_1_1$Prelude__Maybe__Just($cg$3.$1[0]);
                            } else {
                                const $_25_in = $_7_in.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                                let $cg$54 = null;
                                if((((($cg$3.$1.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                                    $cg$54 = true;
                                } else {
                                    $cg$54 = false;
                                }
                                
                                
                                if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$54, true).type === 1)) {
                                    $cg$52 = $HC_0_0$Prelude__Maybe__Nothing;
                                } else {
                                    
                                    if($_25_in.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                                        $cg$52 = new $HC_1_1$Prelude__Maybe__Just($cg$3.$1.slice(1)[0]);
                                    } else {
                                        const $_28_in = $_25_in.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                                        let $cg$57 = null;
                                        if((((($cg$3.$1.slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                                            $cg$57 = true;
                                        } else {
                                            $cg$57 = false;
                                        }
                                        
                                        let $cg$58 = null;
                                        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$57, true).type === 1)) {
                                            $cg$58 = $HC_0_0$Prelude__List__Nil;
                                        } else {
                                            let $cg$59 = null;
                                            if((((($cg$3.$1.slice(1).slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                                                $cg$59 = true;
                                            } else {
                                                $cg$59 = false;
                                            }
                                            
                                            let $cg$60 = null;
                                            if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$59, true).type === 1)) {
                                                $cg$60 = $HC_0_0$Prelude__Strings__StrNil;
                                            } else {
                                                $cg$60 = new $HC_2_1$Prelude__Strings__StrCons($cg$3.$1.slice(1).slice(1).slice(1)[0], $cg$3.$1.slice(1).slice(1).slice(1).slice(1));
                                            }
                                            
                                            $cg$58 = new $HC_2_1$Prelude__List___58__58_($cg$3.$1.slice(1).slice(1)[0], _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$60));
                                        }
                                        
                                        $cg$52 = _95_Data__String__Extra__index_95_with_95_18($cg$58, $_28_in, null);
                                    }
                                }
                            }
                        }
                        
                        
                        if(($cg$52.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_9$DataTypes__LispCharacter($cg$52.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("string-ref: index is out of range"));
                        }
                    } else {
                        const $cg$41 = $_0_arg.$2;
                        const $cg$43 = $cg$41.$1;
                        if(($cg$43.type === 4)) {
                            
                            if(($cg$41.$2.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("string", $_0_arg.$1));
                            } else {
                                const $cg$49 = $_0_arg.$2;
                                
                                if(($cg$49.$2.type === 0)) {
                                    return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$49.$1));
                                } else {
                                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                                }
                            }
                        } else {
                            const $cg$45 = $_0_arg.$2;
                            
                            if(($cg$45.$2.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$45.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    }
                } else {
                    const $cg$29 = $_0_arg.$2;
                    const $cg$31 = $cg$29.$1;
                    if(($cg$31.type === 4)) {
                        
                        if(($cg$29.$2.type === 0)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("string", $_0_arg.$1));
                        } else {
                            const $cg$37 = $_0_arg.$2;
                            
                            if(($cg$37.$2.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$37.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        }
                    } else {
                        const $cg$33 = $_0_arg.$2;
                        
                        if(($cg$33.$2.type === 0)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$33.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            const $cg$5 = $_0_arg.$2;
            if(($cg$5.type === 1)) {
                const $cg$12 = $cg$5.$1;
                if(($cg$12.type === 4)) {
                    
                    if(($cg$5.$2.type === 0)) {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("string", $_0_arg.$1));
                    } else {
                        const $cg$20 = $_0_arg.$1;
                        if(($cg$20.type === 8)) {
                            const $cg$22 = $_0_arg.$2;
                            
                            if(($cg$22.$2.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$22.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    }
                } else {
                    const $cg$14 = $_0_arg.$1;
                    if(($cg$14.type === 8)) {
                        const $cg$16 = $_0_arg.$2;
                        
                        if(($cg$16.$2.type === 0)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$16.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                }
            } else {
                const $cg$7 = $_0_arg.$1;
                if(($cg$7.type === 8)) {
                    const $cg$9 = $_0_arg.$2;
                    if(($cg$9.type === 1)) {
                        
                        if(($cg$9.$2.type === 0)) {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("integer", $cg$9.$1));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Strings.stringToSymbol

function Strings__stringToSymbol($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 8)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_1$DataTypes__LispAtom($cg$3.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("string", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Strings.substring

function Strings__substring($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 8)) {
            const $cg$5 = $_0_arg.$2;
            if(($cg$5.type === 1)) {
                const $cg$7 = $cg$5.$1;
                if(($cg$7.type === 4)) {
                    const $cg$9 = $cg$5.$2;
                    if(($cg$9.type === 1)) {
                        const $cg$11 = $cg$9.$1;
                        if(($cg$11.type === 4)) {
                            
                            if(($cg$9.$2.type === 0)) {
                                const $_10_in = $cg$7.$1;
                                let $cg$13 = null;
                                if((Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Ord_36_Nat_58__33_compare_58_0($_10_in, (new $JSRTS.jsbn.BigInteger(("0")))) > 0)) {
                                    $cg$13 = true;
                                } else {
                                    $cg$13 = Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($_10_in, (new $JSRTS.jsbn.BigInteger(("0"))));
                                }
                                
                                let $cg$14 = null;
                                if($cg$13) {
                                    
                                    if((Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Ord_36_Nat_58__33_compare_58_0($cg$11.$1, (new $JSRTS.jsbn.BigInteger(''+((($cg$3.$1).length))))) < 0)) {
                                        $cg$14 = true;
                                    } else {
                                        $cg$14 = Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($cg$11.$1, (new $JSRTS.jsbn.BigInteger(''+((($cg$3.$1).length)))));
                                    }
                                } else {
                                    $cg$14 = false;
                                }
                                
                                
                                if($cg$14) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_8$DataTypes__LispString(($JSRTS.prim_strSubstr(((($_10_in).intValue()|0)), ((($cg$11.$1.subtract($cg$7.$1)).intValue()|0)), ($cg$3.$1)))));
                                } else {
                                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("substring: ending index is out of range"));
                                }
                            } else {
                                return new $JSRTS.Lazy((function(){
                                    return (function(){
                                        return Strings___123_substring_95_578_125_();
                                    })();
                                }));
                            }
                        } else {
                            return new $JSRTS.Lazy((function(){
                                return (function(){
                                    return Strings___123_substring_95_578_125_();
                                })();
                            }));
                        }
                    } else {
                        return new $JSRTS.Lazy((function(){
                            return (function(){
                                return Strings___123_substring_95_578_125_();
                            })();
                        }));
                    }
                } else {
                    return new $JSRTS.Lazy((function(){
                        return (function(){
                            return Strings___123_substring_95_578_125_();
                        })();
                    }));
                }
            } else {
                return new $JSRTS.Lazy((function(){
                    return (function(){
                        return Strings___123_substring_95_578_125_();
                    })();
                }));
            }
        } else {
            return new $JSRTS.Lazy((function(){
                return (function(){
                    return Strings___123_substring_95_578_125_();
                })();
            }));
        }
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Strings___123_substring_95_578_125_();
            })();
        }));
    }
}

// Symbols.symbolPrimitives

function Symbols__symbolPrimitives(){
    return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("symbol?", $partial_0_1$Symbols__isSymbol()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("symbol->string", $partial_0_1$Symbols__symbolToString()), $HC_0_0$Prelude__List__Nil));
}

// Symbols.symbolToString

function Symbols__symbolToString($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 1)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_8$DataTypes__LispString($cg$3.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Data.SortedMap.toList

function Data__SortedMap__toList($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 0)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        return Data__SortedMap__treeToList_58_treeToList_39__58_0(null, null, null, null, null, $partial_0_1$Data__SortedMap___123_toList_95_585_125_(), $_2_arg.$2);
    }
}

// Data.SortedMap.treeInsert

function Data__SortedMap__treeInsert($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    const $cg$2 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg);
    if(($cg$2.type === 0)) {
        return new $HC_1_0$Prelude__Either__Left($cg$2.$1);
    } else {
        const $cg$4 = $cg$2.$1;
        const $cg$6 = $cg$4.$2;
        return new $HC_1_1$Prelude__Either__Right(new $HC_3_1$Data__SortedMap__Branch2($cg$4.$1, $cg$6.$1, $cg$6.$2));
    }
}

// Data.SortedMap.treeInsert'

function Data__SortedMap__treeInsert_39_($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$36 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$36.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($cg$36.$1, $_6_arg.$2, $_6_arg.$3));
            } else {
                const $cg$38 = $cg$36.$1;
                const $cg$40 = $cg$38.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$38.$1, $cg$40.$1, $cg$40.$2, $_6_arg.$2, $_6_arg.$3));
            }
        } else {
            const $cg$30 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
            if(($cg$30.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$30.$1));
            } else {
                const $cg$32 = $cg$30.$1;
                const $cg$34 = $cg$32.$2;
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$32.$1, $cg$34.$1, $cg$34.$2));
            }
        }
    } else if(($_6_arg.type === 2)) {
        
        
        if($_2_arg.$3($_4_arg)($_6_arg.$2)) {
            const $cg$22 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$1);
            if(($cg$22.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($cg$22.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $_6_arg.$5));
            } else {
                const $cg$24 = $cg$22.$1;
                const $cg$26 = $cg$24.$2;
                return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($cg$24.$1, $cg$26.$1, $cg$26.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$2, new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$3, $_6_arg.$4, $_6_arg.$5))));
            }
        } else {
            
            
            if($_2_arg.$3($_4_arg)($_6_arg.$4)) {
                const $cg$16 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$3);
                if(($cg$16.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $cg$16.$1, $_6_arg.$4, $_6_arg.$5));
                } else {
                    const $cg$18 = $cg$16.$1;
                    const $cg$20 = $cg$18.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $cg$18.$1), new $HC_2_0$Builtins__MkPair($cg$20.$1, new $HC_3_1$Data__SortedMap__Branch2($cg$20.$2, $_6_arg.$4, $_6_arg.$5))));
                }
            } else {
                const $cg$10 = Data__SortedMap__treeInsert_39_(null, null, $_2_arg, null, $_4_arg, $_5_arg, $_6_arg.$5);
                if(($cg$10.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_5_2$Data__SortedMap__Branch3($_6_arg.$1, $_6_arg.$2, $_6_arg.$3, $_6_arg.$4, $cg$10.$1));
                } else {
                    const $cg$12 = $cg$10.$1;
                    const $cg$14 = $cg$12.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_3_1$Data__SortedMap__Branch2($_6_arg.$1, $_6_arg.$2, $_6_arg.$3), new $HC_2_0$Builtins__MkPair($_6_arg.$4, new $HC_3_1$Data__SortedMap__Branch2($cg$12.$1, $cg$14.$1, $cg$14.$2))));
                }
            }
        }
    } else {
        
        const $cg$4 = $_2_arg.$2($_4_arg)($_6_arg.$1);
        if(($cg$4 === 0)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg));
        } else if(($cg$4 > 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2), new $HC_2_0$Builtins__MkPair($_6_arg.$1, new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg))));
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_2_0$Builtins__MkPair(new $HC_2_0$Data__SortedMap__Leaf($_4_arg, $_5_arg), new $HC_2_0$Builtins__MkPair($_4_arg, new $HC_2_0$Data__SortedMap__Leaf($_6_arg.$1, $_6_arg.$2))));
        }
    }
}

// Data.SortedMap.treeLookup

function Data__SortedMap__treeLookup($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    for(;;) {
        
        if(($_5_arg.type === 1)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$3;
            }
        } else if(($_5_arg.type === 2)) {
            
            
            if($_2_arg.$3($_4_arg)($_5_arg.$2)) {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = null;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$1;
            } else {
                
                
                if($_2_arg.$3($_4_arg)($_5_arg.$4)) {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$3;
                } else {
                    $_0_arg = null;
                    $_1_arg = null;
                    $_2_arg = $_2_arg;
                    $_3_arg = null;
                    $_4_arg = $_4_arg;
                    $_5_arg = $_5_arg.$5;
                }
            }
        } else {
            
            
            if($_2_arg.$1($_4_arg)($_5_arg.$1)) {
                return new $HC_1_1$Prelude__Maybe__Just($_5_arg.$2);
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// ParserCombinator.try

function ParserCombinator__try($_0_arg, $_1_arg, $_2_s){
    const $cg$2 = $_1_arg($_2_s);
    if(($cg$2.type === 0)) {
        const $cg$9 = $cg$2.$1;
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair($cg$9.$1, $_2_s));
    } else if(($cg$2.type === 1)) {
        const $cg$4 = $cg$2.$1;
        if(($cg$4.type === 1)) {
            const $cg$6 = $cg$4.$1;
            
            if(($cg$4.$2.type === 0)) {
                return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$6.$1, $cg$6.$2), $HC_0_0$Prelude__List__Nil));
            } else {
                return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_2_s));
            }
        } else {
            return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_2_s));
        }
    } else {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_2_s));
    }
}

// Numbers.unaryTrig

function Numbers__unaryTrig($_0_arg, $_1_arg, $_2_arg){
    
    if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0(Prelude__List__length(null, $_2_arg), (new $JSRTS.jsbn.BigInteger(("1"))))) {
        
        if(($_2_arg.type === 1)) {
            const $cg$4 = $_2_arg.$1;
            if(($cg$4.type === 6)) {
                
                if(($_2_arg.$2.type === 0)) {
                    const $cg$12 = $cg$4.$1;
                    let $cg$11 = null;
                    $cg$11 = $cg$12.$1;
                    const $cg$14 = $cg$4.$1;
                    let $cg$13 = null;
                    $cg$13 = $cg$14.$2;
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex($_1_arg($cg$11)($cg$13)));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
                }
            } else if(($cg$4.type === 5)) {
                
                if(($_2_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat($_0_arg($cg$4.$1)));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
                }
            } else if(($cg$4.type === 4)) {
                
                if(($_2_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat($_0_arg((($cg$4.$1).intValue()))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
                }
            } else if(($cg$4.type === 7)) {
                
                if(($_2_arg.$2.type === 0)) {
                    const $cg$7 = Ratio__rationalCast($cg$4.$1);
                    if(($cg$7.type === 1)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat($_0_arg($cg$7.$1)));
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Numerical input expected"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_2_arg), $_2_arg));
    }
}

// Prelude.Strings.unlines

function Prelude__Strings__unlines($_11_in){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__Strings__unlines_39_(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Prelude__Strings___123_unlines_95_586_125_(), $_11_in)));
}

// Prelude.Strings.unlines'

function Prelude__Strings__unlines_39_($_0_arg){
    
    if(($_0_arg.type === 1)) {
        return Prelude__List___43__43_(null, $_0_arg.$1, new $HC_2_1$Prelude__List___58__58_("\n", Prelude__Strings__unlines_39_($_0_arg.$2)));
    } else {
        return $_0_arg;
    }
}

// Prelude.Strings.unpack

function Prelude__Strings__unpack($_0_arg){
    let $cg$1 = null;
    if((((($_0_arg == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    
    if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true).type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        return new $HC_2_1$Prelude__List___58__58_($_0_arg[0], Prelude__Strings__unpack($_0_arg.slice(1)));
    }
}

// Strings.unpackStr

function Strings__unpackStr($_0_arg){
    
    if(($_0_arg.type === 8)) {
        return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("string", $_0_arg));
    }
}

// Prelude.Strings.unwords

function Prelude__Strings__unwords($_37_in){
    let $cg$1 = null;
    if((Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Prelude__Strings___123_unwords_95_587_125_(), $_37_in).type === 0)) {
        $cg$1 = Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Prelude__Strings___123_unwords_95_587_125_(), $_37_in);
    } else {
        $cg$1 = Prelude__Strings__foldr1(null, $partial_0_2$Prelude__Strings___123_unwords_95_588_125_(), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Prelude__Strings___123_unwords_95_587_125_(), $_37_in));
    }
    
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", $cg$1);
}

// Vector.vectorLength

function Vector__vectorLength($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 0)) {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(''+($cg$3.$1)))));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Vector", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(1, 1), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Vector.vectorPrimitives

function Vector__vectorPrimitives(){
    return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("vector?", $partial_0_1$Vector__isVector()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("vector-length", $partial_0_1$Vector__vectorLength()), new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("vector-ref", $partial_0_1$Vector__vectorRef()), $HC_0_0$Prelude__List__Nil)));
}

// Vector.vectorRef

function Vector__vectorRef($_0_arg){
    
    if(($_0_arg.type === 1)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 0)) {
            const $cg$6 = $_0_arg.$2;
            if(($cg$6.type === 1)) {
                const $cg$8 = $cg$6.$1;
                if(($cg$8.type === 4)) {
                    
                    if(($cg$6.$2.type === 0)) {
                        const $cg$11 = Prelude__List__index_39_(null, $cg$8.$1, $cg$3.$2);
                        if(($cg$11.type === 1)) {
                            return new $HC_1_1$Prelude__Either__Right($cg$11.$1);
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(Vector__outOfBoundsError("vector-ref", $cg$8.$1, $cg$3.$2));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
                }
            } else if(($cg$6.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Vector", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        } else {
            
            if(($_0_arg.$2.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("Vector", $_0_arg.$1));
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
            }
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_0_arg), $_0_arg));
    }
}

// Prelude.List.zipWith

function Prelude__List__zipWith($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        if(($_4_arg.type === 1)) {
            return new $HC_2_1$Prelude__List___58__58_($_3_arg($_4_arg.$1)($_5_arg.$1), Prelude__List__zipWith(null, null, null, $_3_arg, $_4_arg.$2, $_5_arg.$2));
        } else {
            return $_4_arg;
        }
    } else {
        
        if(($_4_arg.type === 1)) {
            return $HC_0_0$Prelude__List__Nil;
        } else {
            return $_4_arg;
        }
    }
}

// Lists.{accessors_0}

function Lists___123_accessors_95_0_125_($_0_lift){
    return new $HC_2_0$Builtins__MkPair(("c" + (Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", $_0_lift) + "r")), Lists__accessors_58_makeAccessor_58_0($_0_lift));
}

// Eval.{apply'_1}

function Eval___123_apply_39__95_1_125_($_0_lift, $_1_lift){
    return new $HC_2_0$Builtins__MkPair($_0_lift, $_1_lift);
}

// Eval.{apply'_2}

function Eval___123_apply_39__95_2_125_(){
    throw new Error(  "*** Eval.idr:90:28-45:unmatched case in Eval.case block in apply\' at Eval.idr:90:28-45 ***");
}

// Eval.{apply'_3}

function Eval___123_apply_39__95_3_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return new $HC_1_0$Control__ST__Pure(Prelude__List__last(null, new $HC_2_1$Prelude__List___58__58_($_0_lift.$1, $_0_lift.$2), null));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_apply_39__95_2_125_();
            })();
        }));
    }
}

// Eval.{apply'_4}

function Eval___123_apply_39__95_4_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__apply_39__58_evalBody_58_1(null, null, null, null, null, null, null, null, $_0_lift, $_2_lift, $_1_lift), $partial_0_1$Eval___123_apply_39__95_3_125_());
}

// ParseNumber.{binConverter_5}

function ParseNumber___123_binConverter_95_5_125_(){
    throw new Error(  "*** ParseNumber.idr:74:23:unmatched case in ParseNumber.case block in binConverter at ParseNumber.idr:74:23 ***");
}

// Parse.{bracketed_6}

function Parse___123_bracketed_95_6_125_($_0_lift){
    return ($_0_lift === "(");
}

// Parse.{bracketed_7}

function Parse___123_bracketed_95_7_125_($_0_lift){
    return ($_0_lift === "[");
}

// Parse.{bracketed_8}

function Parse___123_bracketed_95_8_125_($_0_lift){
    return ($_0_lift === "{");
}

// Parse.{bracketed_9}

function Parse___123_bracketed_95_9_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_0_lift, $_2_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{bracketed_10}

function Parse___123_bracketed_95_10_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__matchBracket($_0_lift), $partial_1_3$Parse___123_bracketed_95_9_125_($_1_lift));
}

// Parse.{bracketed_11}

function Parse___123_bracketed_95_11_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_0_lift, $partial_1_2$Parse___123_bracketed_95_10_125_($_1_lift));
}

// Lists.{cdr_12}

function Lists___123_cdr_95_12_125_($_0_lift){
    return $JSRTS.force($_0_lift);
}

// Lists.{cons_14}

function Lists___123_cons_95_14_125_($_0_lift){
    return $_0_lift;
}

// ParseNumber.{decConverter_15}

function ParseNumber___123_decConverter_95_15_125_(){
    throw new Error(  "*** ParseNumber.idr:31:23:unmatched case in ParseNumber.case block in decConverter at ParseNumber.idr:31:23 ***");
}

// Prelude.Interfaces.{divBigInt_16}

function Prelude__Interfaces___123_divBigInt_95_16_125_(){
    throw new Error(  "*** ./Prelude/Interfaces.idr:341:22-27:unmatched case in Prelude.Interfaces.case block in divBigInt at ./Prelude/Interfaces.idr:341:22-27 ***");
}

// ParserCombinator.{endBy_20}

function ParserCombinator___123_endBy_95_20_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_0_lift, $partial_1_3$Parse___123_bracketed_95_9_125_($_1_lift));
}

// Eval.{ensureAtoms_21}

function Eval___123_ensureAtoms_95_21_125_($_0_lift, $_1_lift, $_2_lift){
    return Eval__ensureAtoms(null, $_0_lift, $_1_lift);
}

// Primitives.{eqv_22}

function Primitives___123_eqv_95_22_125_($_0_lift, $_1_lift){
    return ($_0_lift === $_1_lift);
}

// Eval.{eval_23}

function Eval___123_eval_95_23_125_($_0_lift, $_1_lift, $_2_lift){
    
    if(($_2_lift.type === 1)) {
        return new $HC_1_0$Control__ST__Pure($_2_lift.$1);
    } else {
        
        return $_0_lift.$1(null)(null)(new $HC_1_6$DataTypes__Default(("Unknown atom: " + $_1_lift)));
    }
}

// Eval.{eval_24}

function Eval___123_eval_95_24_125_($_0_lift){
    return $partial_0_1$DataTypes__showVal();
}

// Eval.{eval_25}

function Eval___123_eval_95_25_125_($_0_lift){
    return new $HC_1_0$Control__ST__Pure($_0_lift);
}

// Eval.{eval_26}

function Eval___123_eval_95_26_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__apply_39_(null, $_0_lift, $_1_lift, $_2_lift), $partial_0_1$Eval___123_eval_95_25_125_());
}

// Eval.{eval_27}

function Eval___123_eval_95_27_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval_58_unpackArgs_58_26(null, null, null, null, $_0_lift, $_2_lift), $partial_2_3$Eval___123_eval_95_26_125_($_0_lift, $_1_lift));
}

// Eval.{eval_28}

function Eval___123_eval_95_28_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__evalArgs(null, $_0_lift, $_1_lift, new $HC_2_1$Prelude__List___58__58_($_2_lift, $HC_0_0$Prelude__List__Nil)), $partial_2_3$Eval___123_eval_95_27_125_($_0_lift, $_3_lift));
}

// Eval.{eval_29}

function Eval___123_eval_95_29_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_0_lift, $_1_lift, $_2_lift), $partial_3_4$Eval___123_eval_95_28_125_($_0_lift, $_1_lift, $_3_lift));
}

// Eval.{eval_33}

function Eval___123_eval_95_33_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__evalArgs(null, $_0_lift, $_1_lift, $_2_lift), $partial_2_3$Eval___123_eval_95_26_125_($_0_lift, $_3_lift));
}

// Eval.{eval_34}

function Eval___123_eval_95_34_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_0_lift, $_1_lift, $_2_lift), $partial_3_4$Eval___123_eval_95_33_125_($_0_lift, $_1_lift, $_3_lift));
}

// Eval.{eval_45}

function Eval___123_eval_95_45_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Eval__eval_58_evalClauses_58_12(null, $_0_lift, null, null, $_1_lift, $_3_lift, $_2_lift);
}

// Eval.{eval_46}

function Eval___123_eval_95_46_125_($_0_lift){
    return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
}

// Eval.{eval_47}

function Eval___123_eval_95_47_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$3;
    $cg$1 = $cg$3.$5($_1_lift)($_2_lift)($_3_lift);
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_0_1$Eval___123_eval_95_46_125_());
}

// Eval.{eval_90}

function Eval___123_eval_95_90_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 10)) {
        
        if((!$_4_lift.$1)) {
            return Eval__eval(null, $_0_lift, $_1_lift, $_2_lift);
        } else {
            return Eval__eval(null, $_0_lift, $_1_lift, $_3_lift);
        }
    } else {
        return Eval__eval(null, $_0_lift, $_1_lift, $_3_lift);
    }
}

// Eval.{eval_112}

function Eval___123_eval_95_112_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_1_0$Control__ST__Pure(new $HC_5_12$DataTypes__LispFunc("\u03bb", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), $_0_lift), $HC_0_0$Prelude__Maybe__Nothing, $_1_lift, $_2_lift));
}

// Eval.{eval_123}

function Eval___123_eval_95_123_125_(){
    throw new Error(  "*** Eval.idr:59:1-33:unmatched case in Eval.extractVar ***");
}

// Eval.{eval_124}

function Eval___123_eval_95_124_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift.type === 1)) {
        $cg$1 = $_0_lift.$1;
    } else {
        $cg$1 = new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_123_125_();
            })();
        }));
    }
    
    return new $HC_2_0$Builtins__MkPair($cg$1, $_1_lift);
}

// Eval.{eval_125}

function Eval___123_eval_95_125_125_($_0_lift, $_1_lift, $_2_lift){
    return Eval__evalList(null, $_0_lift, $_2_lift, $_1_lift);
}

// Eval.{eval_126}

function Eval___123_eval_95_126_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$3;
    $cg$1 = $cg$3.$6($_1_lift)(Prelude__List__zipWith(null, null, null, $partial_0_2$Eval___123_eval_95_124_125_(), $_2_lift, $_4_lift));
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_2_3$Eval___123_eval_95_125_125_($_0_lift, $_3_lift));
}

// Eval.{eval_127}

function Eval___123_eval_95_127_125_(){
    throw new Error(  "*** Eval.idr:271:30-43:unmatched case in Eval.case block in case block in eval at Eval.idr:269:31-44 at Eval.idr:271:30-43 ***");
}

// Eval.{eval_128}

function Eval___123_eval_95_128_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        return new $HC_2_1$Control__ST__Bind(Eval__evalArgs(null, $_0_lift, $_1_lift, $_4_lift.$1), $partial_4_5$Eval___123_eval_95_126_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_127_125_();
            })();
        }));
    }
}

// Eval.{eval_129}

function Eval___123_eval_95_129_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__getTails(null, $_0_lift, $_1_lift), $partial_4_5$Eval___123_eval_95_128_125_($_0_lift, $_2_lift, $_3_lift, $_4_lift));
}

// Eval.{eval_130}

function Eval___123_eval_95_130_125_(){
    throw new Error(  "*** Eval.idr:269:31-44:unmatched case in Eval.case block in eval at Eval.idr:269:31-44 ***");
}

// Eval.{eval_131}

function Eval___123_eval_95_131_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        return new $HC_2_1$Control__ST__Bind(Eval__ensureAtoms(null, $_0_lift, $_4_lift.$1), $partial_5_6$Eval___123_eval_95_129_125_($_0_lift, $_1_lift, $_2_lift, $_4_lift.$1, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_130_125_();
            })();
        }));
    }
}

// Eval.{eval_142}

function Eval___123_eval_95_142_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Eval__evalList(null, $_0_lift, $_1_lift, $_2_lift);
}

// Eval.{eval_143}

function Eval___123_eval_95_143_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval_58_buildEnv_58_23(null, null, null, null, $_0_lift, $_4_lift, $_1_lift, $_2_lift), $partial_3_4$Eval___123_eval_95_142_125_($_0_lift, $_4_lift, $_3_lift));
}

// Eval.{eval_144}

function Eval___123_eval_95_144_125_(){
    throw new Error(  "*** Eval.idr:278:30-43:unmatched case in Eval.case block in case block in eval at Eval.idr:276:31-44 at Eval.idr:278:30-43 ***");
}

// Eval.{eval_145}

function Eval___123_eval_95_145_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        let $cg$2 = null;
        const $cg$4 = $_0_lift.$3;
        $cg$2 = $cg$4.$6($_1_lift)($HC_0_0$Prelude__List__Nil);
        return new $HC_2_1$Control__ST__Bind($cg$2, $partial_4_5$Eval___123_eval_95_143_125_($_0_lift, $_2_lift, $_4_lift.$1, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_144_125_();
            })();
        }));
    }
}

// Eval.{eval_146}

function Eval___123_eval_95_146_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__getTails(null, $_0_lift, $_1_lift), $partial_4_5$Eval___123_eval_95_145_125_($_0_lift, $_2_lift, $_3_lift, $_4_lift));
}

// Eval.{eval_147}

function Eval___123_eval_95_147_125_(){
    throw new Error(  "*** Eval.idr:276:31-44:unmatched case in Eval.case block in eval at Eval.idr:276:31-44 ***");
}

// Eval.{eval_148}

function Eval___123_eval_95_148_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        return new $HC_2_1$Control__ST__Bind(Eval__ensureAtoms(null, $_0_lift, $_4_lift.$1), $partial_5_6$Eval___123_eval_95_146_125_($_0_lift, $_1_lift, $_2_lift, $_4_lift.$1, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_147_125_();
            })();
        }));
    }
}

// Eval.{eval_160}

function Eval___123_eval_95_160_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift.type === 1)) {
        $cg$1 = $_0_lift.$1;
    } else {
        $cg$1 = new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_123_125_();
            })();
        }));
    }
    
    return new $HC_2_0$Builtins__MkPair($cg$1, $_1_lift);
}

// Eval.{eval_162}

function Eval___123_eval_95_162_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval_58_setRec_58_24(null, null, null, null, $_0_lift, $_1_lift, Prelude__List__zipWith(null, null, null, $partial_0_2$Eval___123_eval_95_160_125_(), $_2_lift, $_4_lift)), $partial_3_4$Eval___123_eval_95_142_125_($_0_lift, $_1_lift, $_3_lift));
}

// Eval.{eval_163}

function Eval___123_eval_95_163_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__evalArgs(null, $_0_lift, $_1_lift, $_2_lift), $partial_4_5$Eval___123_eval_95_162_125_($_0_lift, $_1_lift, $_3_lift, $_4_lift));
}

// Eval.{eval_164}

function Eval___123_eval_95_164_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval_58_buildEnv_58_24(null, null, null, null, $_0_lift, $_4_lift, $_1_lift), $partial_5_6$Eval___123_eval_95_163_125_($_0_lift, $_4_lift, $_2_lift, $_1_lift, $_3_lift));
}

// Eval.{eval_165}

function Eval___123_eval_95_165_125_(){
    throw new Error(  "*** Eval.idr:293:30-43:unmatched case in Eval.case block in case block in eval at Eval.idr:291:31-44 at Eval.idr:293:30-43 ***");
}

// Eval.{eval_166}

function Eval___123_eval_95_166_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        let $cg$2 = null;
        const $cg$4 = $_0_lift.$3;
        $cg$2 = $cg$4.$6($_1_lift)($HC_0_0$Prelude__List__Nil);
        return new $HC_2_1$Control__ST__Bind($cg$2, $partial_4_5$Eval___123_eval_95_164_125_($_0_lift, $_2_lift, $_4_lift.$1, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_165_125_();
            })();
        }));
    }
}

// Eval.{eval_167}

function Eval___123_eval_95_167_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__getTails(null, $_0_lift, $_1_lift), $partial_4_5$Eval___123_eval_95_166_125_($_0_lift, $_2_lift, $_3_lift, $_4_lift));
}

// Eval.{eval_168}

function Eval___123_eval_95_168_125_(){
    throw new Error(  "*** Eval.idr:291:31-44:unmatched case in Eval.case block in eval at Eval.idr:291:31-44 ***");
}

// Eval.{eval_169}

function Eval___123_eval_95_169_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 2)) {
        return new $HC_2_1$Control__ST__Bind(Eval__ensureAtoms(null, $_0_lift, $_4_lift.$1), $partial_5_6$Eval___123_eval_95_167_125_($_0_lift, $_1_lift, $_2_lift, $_4_lift.$1, $_3_lift));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_168_125_();
            })();
        }));
    }
}

// Eval.{eval_181}

function Eval___123_eval_95_181_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    $cg$1 = $_0_lift.$2(null)((DataTypes__showVal($_1_lift) + "\n"));
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_0_1$Eval___123_eval_95_46_125_());
}

// Eval.{eval_203}

function Eval___123_eval_95_203_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$3;
    $cg$1 = $cg$3.$4($_1_lift)($_2_lift)($_3_lift);
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_0_1$Eval___123_eval_95_46_125_());
}

// Eval.{eval_225}

function Eval___123_eval_95_225_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__eval_58_setCar_58_15(null, null, $_0_lift, $_1_lift, $_2_lift, $_3_lift, $_5_lift, $_4_lift), $partial_0_1$Eval___123_eval_95_46_125_());
}

// Eval.{eval_226}

function Eval___123_eval_95_226_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$3;
    $cg$1 = $cg$3.$3($_1_lift)($_2_lift);
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_5_6$Eval___123_eval_95_225_125_($_2_lift, $_3_lift, $_0_lift, $_1_lift, $_4_lift));
}

// Eval.{evalArgs_257}

function Eval___123_evalArgs_95_257_125_($_0_lift, $_1_lift){
    return new $HC_1_0$Control__ST__Pure(new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift));
}

// Eval.{evalArgs_258}

function Eval___123_evalArgs_95_258_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__evalArgs(null, $_0_lift, $_1_lift, $_2_lift), $partial_1_2$Eval___123_evalArgs_95_257_125_($_3_lift));
}

// Repl.{evalExprList_260}

function Repl___123_evalExprList_95_260_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Control__ST__Bind(Repl__evalExprList_58_traverse_39__58_0(null, null, null, null, null, null, $partial_3_4$Eval__eval(null, $_0_lift, $_1_lift), $_2_lift), $partial_0_1$Eval___123_eval_95_25_125_());
}

// Prelude.Strings.{foldr1_263}

function Prelude__Strings___123_foldr1_95_263_125_(){
    throw new Error(  "*** ./Prelude/Strings.idr:24:1-16:unmatched case in Prelude.Strings.foldr1 ***");
}

// Data.SortedMap.{fromList_264}

function Data__SortedMap___123_fromList_95_264_125_($_0_lift, $_1_lift){
    
    return Data__SortedMap__insert(null, null, $_1_lift.$1, $_1_lift.$2, $_0_lift);
}

// Eval.{getHeads_265}

function Eval___123_getHeads_95_265_125_(){
    throw new Error(  "*** Eval.idr:37:22-32:unmatched case in Eval.case block in getHeads at Eval.idr:37:22-32 ***");
}

// Eval.{getHeads_266}

function Eval___123_getHeads_95_266_125_($_0_lift, $_1_lift){
    
    if(($_1_lift.type === 2)) {
        return new $HC_1_0$Control__ST__Pure(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift.$1)));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_getHeads_95_265_125_();
            })();
        }));
    }
}

// Eval.{getTails_267}

function Eval___123_getTails_95_267_125_(){
    throw new Error(  "*** Eval.idr:44:22-32:unmatched case in Eval.case block in getTails at Eval.idr:44:22-32 ***");
}

// Eval.{getTails_268}

function Eval___123_getTails_95_268_125_($_0_lift, $_1_lift){
    
    if(($_1_lift.type === 2)) {
        return new $HC_1_0$Control__ST__Pure(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift.$1)));
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_getTails_95_267_125_();
            })();
        }));
    }
}

// ParseNumber.{hexConverter_269}

function ParseNumber___123_hexConverter_95_269_125_(){
    throw new Error(  "*** ParseNumber.idr:55:23-33:unmatched case in ParseNumber.case block in hexConverter at ParseNumber.idr:55:23-33 ***");
}

// Util.{initEnv'_270}

function Util___123_initEnv_39__95_270_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $_10_in = $_3_lift($_4_lift);
    return $_2_lift($_10_in);
}

// Util.{initEnv'_271}

function Util___123_initEnv_39__95_271_125_($_0_lift, $_1_lift, $_2_lift){
    return $_1_lift;
}

// Util.{initEnv'_272}

function Util___123_initEnv_39__95_272_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $_19_in = $_2_lift($_4_lift);
    const $_20_in = $_3_lift($_4_lift);
    return $_19_in($_20_in);
}

// Util.{initEnv'_273}

function Util___123_initEnv_39__95_273_125_($_0_lift, $_1_lift){
    return ($_0_lift == $_1_lift);
}

// Util.{initEnv'_274}

function Util___123_initEnv_39__95_274_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift);
}

// Util.{initEnv'_275}

function Util___123_initEnv_39__95_275_125_($_0_lift, $_1_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) < 0)) {
        return true;
    } else {
        return ($_0_lift == $_1_lift);
    }
}

// Lists.{listPrimitives_276}

function Lists___123_listPrimitives_95_276_125_($_0_lift){
    return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($_0_lift));
}

// ParserCombinator.{many'_277}

function ParserCombinator___123_many_39__95_277_125_($_0_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($HC_0_0$Prelude__List__Nil, $_0_lift), $HC_0_0$Prelude__List__Nil));
}

// ParserCombinator.{many1_278}

function ParserCombinator___123_many1_95_278_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift), $_2_lift), $HC_0_0$Prelude__List__Nil));
}

// ParserCombinator.{many1_279}

function ParserCombinator___123_many1_95_279_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many_39_(null, $_0_lift), $partial_1_3$ParserCombinator___123_many1_95_278_125_($_1_lift));
}

// Parse.{matchBracket_280}

function Parse___123_matchBracket_95_280_125_($_0_lift){
    return ($_0_lift === ")");
}

// Parse.{matchBracket_281}

function Parse___123_matchBracket_95_281_125_($_0_lift){
    return ($_0_lift === "]");
}

// Parse.{matchBracket_282}

function Parse___123_matchBracket_95_282_125_($_0_lift){
    return ($_0_lift === "}");
}

// Parse.{matchBracket_283}

function Parse___123_matchBracket_95_283_125_(){
    throw new Error(  "*** Parse.idr:15:10-13:unmatched case in Parse.case block in matchBracket at Parse.idr:15:10-13 ***");
}

// Prelude.Interfaces.{modBigInt_284}

function Prelude__Interfaces___123_modBigInt_95_284_125_(){
    throw new Error(  "*** ./Prelude/Interfaces.idr:345:22-27:unmatched case in Prelude.Interfaces.case block in modBigInt at ./Prelude/Interfaces.idr:345:22-27 ***");
}

// Numbers.{numBoolBinop_285}

function Numbers___123_numBoolBinop_95_285_125_(){
    throw new Error(  "*** Numbers.idr:231:24-37:unmatched case in Numbers.case block in numBoolBinop at Numbers.idr:231:24-37 ***");
}

// Numbers.{numCast_289}

function Numbers___123_numCast_95_289_125_($_0_lift, $_1_lift){
    return $_0_lift.add($_1_lift);
}

// Numbers.{numCast_290}

function Numbers___123_numCast_95_290_125_($_0_lift, $_1_lift){
    return $_0_lift.multiply($_1_lift);
}

// Numbers.{numCast_292}

function Numbers___123_numCast_95_292_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__divBigInt($_0_lift, $_1_lift);
}

// Numbers.{numCast_293}

function Numbers___123_numCast_95_293_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__modBigInt($_0_lift, $_1_lift);
}

// Numbers.{numCast_294}

function Numbers___123_numCast_95_294_125_($_0_lift, $_1_lift){
    return $_0_lift.equals($_1_lift);
}

// Numbers.{numCast_298}

function Numbers___123_numCast_95_298_125_($_0_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_lift, (new $JSRTS.jsbn.BigInteger(("0")))) < 0)) {
        return (new $JSRTS.jsbn.BigInteger(("0"))).subtract($_0_lift);
    } else {
        return $_0_lift;
    }
}

// Numbers.{numCast_300}

function Numbers___123_numCast_95_300_125_($_0_lift, $_1_lift){
    return Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_lift, $_1_lift);
}

// Numbers.{numCast_301}

function Numbers___123_numCast_95_301_125_($_0_lift, $_1_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_lift, $_1_lift) < 0)) {
        return true;
    } else {
        return $_0_lift.equals($_1_lift);
    }
}

// Numbers.{numCast_305}

function Numbers___123_numCast_95_305_125_($_0_lift, $_1_lift){
    return $_0_lift.subtract($_1_lift);
}

// Numbers.{numCos_323}

function Numbers___123_numCos_95_323_125_($_0_lift){
    return Math.cos($_0_lift);
}

// Numbers.{numCos_324}

function Numbers___123_numCos_95_324_125_($_0_lift, $_1_lift){
    return new $HC_2_0$Data__Complex___58__43_((Math.cos($_0_lift) * ((Math.exp($_1_lift) + Math.exp((-($_1_lift)))) / 2.0)), (-1.0 * (Math.sin($_0_lift) * ((Math.exp($_1_lift) - Math.exp((-($_1_lift)))) / 2.0))));
}

// Numbers.{numPrimitives_325}

function Numbers___123_numPrimitives_95_325_125_($_0_lift){
    return Numbers__variadicNumberOp_58_helper_58_0(null, $partial_0_1$Numbers__numAdd_58_doAdd_58_0(), null, $_0_lift, new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(("0")))));
}

// Numbers.{numPrimitives_326}

function Numbers___123_numPrimitives_95_326_125_($_0_lift){
    
    if(($_0_lift.type === 0)) {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(("1")))));
    } else {
        return Numbers__variadicNumberOp_58_helper_58_0(null, $partial_1_2$Numbers__numMul_58_doMul_58_1(null), null, $_0_lift, new $HC_1_4$DataTypes__LispInteger((new $JSRTS.jsbn.BigInteger(("1")))));
    }
}

// Numbers.{numPrimitives_327}

function Numbers___123_numPrimitives_95_327_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__variadicNumberOp_58_helper_58_0(null, $partial_2_3$Numbers__numDiv_58_doDiv_58_1(null, null), null, $_0_lift.$2, $_0_lift.$1);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_328}

function Numbers___123_numPrimitives_95_328_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        const $cg$3 = $_0_lift.$1;
        if(($cg$3.type === 6)) {
            
            if(($_0_lift.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                
                if(($_0_lift.type === 1)) {
                    const $cg$19 = $_0_lift.$1;
                    if(($cg$19.type === 5)) {
                        
                        if(($_0_lift.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                        } else {
                            
                            if(($_0_lift.type === 1)) {
                                const $cg$27 = $_0_lift.$1;
                                if(($cg$27.type === 7)) {
                                    
                                    if(($_0_lift.$2.type === 0)) {
                                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                    } else {
                                        return Numbers__isInteger($_0_lift);
                                    }
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        }
                    } else {
                        
                        if(($_0_lift.type === 1)) {
                            const $cg$22 = $_0_lift.$1;
                            if(($cg$22.type === 7)) {
                                
                                if(($_0_lift.$2.type === 0)) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    }
                } else {
                    return Numbers__isInteger($_0_lift);
                }
            }
        } else {
            
            if(($_0_lift.type === 1)) {
                const $cg$6 = $_0_lift.$1;
                if(($cg$6.type === 5)) {
                    
                    if(($_0_lift.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                    } else {
                        
                        if(($_0_lift.type === 1)) {
                            const $cg$14 = $_0_lift.$1;
                            if(($cg$14.type === 7)) {
                                
                                if(($_0_lift.$2.type === 0)) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    }
                } else {
                    
                    if(($_0_lift.type === 1)) {
                        const $cg$9 = $_0_lift.$1;
                        if(($cg$9.type === 7)) {
                            
                            if(($_0_lift.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    } else {
                        return Numbers__isInteger($_0_lift);
                    }
                }
            } else {
                return Numbers__isInteger($_0_lift);
            }
        }
    } else {
        return Numbers__isInteger($_0_lift);
    }
}

// Numbers.{numPrimitives_329}

function Numbers___123_numPrimitives_95_329_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        const $cg$3 = $_0_lift.$1;
        if(($cg$3.type === 6)) {
            
            if(($_0_lift.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                
                if(($_0_lift.type === 1)) {
                    const $cg$19 = $_0_lift.$1;
                    if(($cg$19.type === 5)) {
                        
                        if(($_0_lift.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                        } else {
                            
                            if(($_0_lift.type === 1)) {
                                const $cg$27 = $_0_lift.$1;
                                if(($cg$27.type === 7)) {
                                    
                                    if(($_0_lift.$2.type === 0)) {
                                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                    } else {
                                        return Numbers__isInteger($_0_lift);
                                    }
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        }
                    } else {
                        
                        if(($_0_lift.type === 1)) {
                            const $cg$22 = $_0_lift.$1;
                            if(($cg$22.type === 7)) {
                                
                                if(($_0_lift.$2.type === 0)) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    }
                } else {
                    return Numbers__isInteger($_0_lift);
                }
            }
        } else {
            
            if(($_0_lift.type === 1)) {
                const $cg$6 = $_0_lift.$1;
                if(($cg$6.type === 5)) {
                    
                    if(($_0_lift.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                    } else {
                        
                        if(($_0_lift.type === 1)) {
                            const $cg$14 = $_0_lift.$1;
                            if(($cg$14.type === 7)) {
                                
                                if(($_0_lift.$2.type === 0)) {
                                    return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                                } else {
                                    return Numbers__isInteger($_0_lift);
                                }
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    }
                } else {
                    
                    if(($_0_lift.type === 1)) {
                        const $cg$9 = $_0_lift.$1;
                        if(($cg$9.type === 7)) {
                            
                            if(($_0_lift.$2.type === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                            } else {
                                return Numbers__isInteger($_0_lift);
                            }
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    } else {
                        return Numbers__isInteger($_0_lift);
                    }
                }
            } else {
                return Numbers__isInteger($_0_lift);
            }
        }
    } else {
        return Numbers__isInteger($_0_lift);
    }
}

// Numbers.{numPrimitives_330}

function Numbers___123_numPrimitives_95_330_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        const $cg$3 = $_0_lift.$1;
        if(($cg$3.type === 5)) {
            
            if(($_0_lift.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                
                if(($_0_lift.type === 1)) {
                    const $cg$11 = $_0_lift.$1;
                    if(($cg$11.type === 7)) {
                        
                        if(($_0_lift.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                        } else {
                            return Numbers__isInteger($_0_lift);
                        }
                    } else {
                        return Numbers__isInteger($_0_lift);
                    }
                } else {
                    return Numbers__isInteger($_0_lift);
                }
            }
        } else {
            
            if(($_0_lift.type === 1)) {
                const $cg$6 = $_0_lift.$1;
                if(($cg$6.type === 7)) {
                    
                    if(($_0_lift.$2.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
                    } else {
                        return Numbers__isInteger($_0_lift);
                    }
                } else {
                    return Numbers__isInteger($_0_lift);
                }
            } else {
                return Numbers__isInteger($_0_lift);
            }
        }
    } else {
        return Numbers__isInteger($_0_lift);
    }
}

// Numbers.{numPrimitives_331}

function Numbers___123_numPrimitives_95_331_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        const $cg$3 = $_0_lift.$1;
        if(($cg$3.type === 7)) {
            
            if(($_0_lift.$2.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(true));
            } else {
                return Numbers__isInteger($_0_lift);
            }
        } else {
            return Numbers__isInteger($_0_lift);
        }
    } else {
        return Numbers__isInteger($_0_lift);
    }
}

// Numbers.{numPrimitives_332}

function Numbers___123_numPrimitives_95_332_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop("=", $partial_2_4$Numbers__numBoolBinopEq_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_333}

function Numbers___123_numPrimitives_95_333_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop("/=", $partial_2_4$Numbers__numBoolBinopNeq_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_334}

function Numbers___123_numPrimitives_95_334_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop(">", $partial_2_4$Numbers__numBoolBinopGt_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_335}

function Numbers___123_numPrimitives_95_335_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop("<", $partial_2_4$Numbers__numBoolBinopLt_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_336}

function Numbers___123_numPrimitives_95_336_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop(">=", $partial_2_4$Numbers__numBoolBinopGte_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numPrimitives_337}

function Numbers___123_numPrimitives_95_337_125_($_0_lift){
    
    if(($_0_lift.type === 1)) {
        return Numbers__numBoolBinop("<=", $partial_2_4$Numbers__numBoolBinopLte_58_fn_58_1(null, null), $_0_lift.$1, $_0_lift.$2);
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_3_0$DataTypes__NumArgs(new $HC_1_0$DataTypes__Min(1), (new $JSRTS.jsbn.BigInteger(("0"))), $HC_0_0$Prelude__List__Nil));
    }
}

// Numbers.{numSine_338}

function Numbers___123_numSine_95_338_125_($_0_lift){
    return Math.sin($_0_lift);
}

// Numbers.{numSine_339}

function Numbers___123_numSine_95_339_125_($_0_lift, $_1_lift){
    return new $HC_2_0$Data__Complex___58__43_((Math.sin($_0_lift) * ((Math.exp($_1_lift) + Math.exp((-($_1_lift)))) / 2.0)), (Math.cos($_0_lift) * ((Math.exp($_1_lift) - Math.exp((-($_1_lift)))) / 2.0)));
}

// Numbers.{numToString_340}

function Numbers___123_numToString_95_340_125_(){
    throw new Error(  "*** Numbers.idr:342:1-347:46:unmatched case in Numbers.numToString ***");
}

// ParseNumber.{octConverter_342}

function ParseNumber___123_octConverter_95_342_125_(){
    throw new Error(  "*** ParseNumber.idr:44:23:unmatched case in ParseNumber.case block in octConverter at ParseNumber.idr:44:23 ***");
}

// ParserCombinator.{oneOf_343}

function ParserCombinator___123_oneOf_95_343_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift === "")) {
        $cg$1 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the head of an empty string"));
    } else {
        $cg$1 = $_0_lift[0];
    }
    
    return ($_1_lift === $cg$1);
}

// Parse.{parseAtom_344}

function Parse___123_parseAtom_95_344_125_($_0_lift){
    
    if(Prelude__Chars__isUpper($_0_lift)) {
        return true;
    } else {
        return Prelude__Chars__isLower($_0_lift);
    }
}

// Parse.{parseAtom_346}

function Parse___123_parseAtom_95_346_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift === "#f")) {
        $cg$1 = new $HC_1_10$DataTypes__LispBool(false);
    } else if(($_0_lift === "#t")) {
        $cg$1 = new $HC_1_10$DataTypes__LispBool(true);
    } else {
        $cg$1 = new $HC_1_1$DataTypes__LispAtom($_0_lift);
    }
    
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$1, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseAtom_347}

function Parse___123_parseAtom_95_347_125_($_0_lift, $_1_lift){
    const $_4_in = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift));
    return $partial_1_2$Parse___123_parseAtom_95_346_125_($_4_in);
}

// Parse.{parseAtom_348}

function Parse___123_parseAtom_95_348_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many_39_(null, $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Parse___123_parseAtom_95_344_125_()), $partial_3_4$ParserCombinator___60__124__62_(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isDigit()), ParserCombinator__oneOf("!#$%&|*+-/:<=>?@^_~")))), $partial_1_2$Parse___123_parseAtom_95_347_125_($_0_lift));
}

// Parse.{parseBlockComment_349}

function Parse___123_parseBlockComment_95_349_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($HC_0_13$DataTypes__LispVoid, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseBlockComment_350}

function Parse___123_parseBlockComment_95_350_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipUntil_58_scan_58_0(null, null, ParserCombinator__string("|#"), $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseBlockComment(), Parse__parseBlockComment_58_takeAnything_58_0())), $partial_0_2$Parse___123_parseBlockComment_95_349_125_());
}

// Parse.{parseCharacter_352}

function Parse___123_parseCharacter_95_352_125_($_0_lift){
    
    if(Prelude__Chars__isUpper($_0_lift)) {
        return String.fromCharCode(((($_0_lift).charCodeAt(0)|0) + 32));
    } else {
        return $_0_lift;
    }
}

// Parse.{parseCharacter_353}

function Parse___123_parseCharacter_95_353_125_(){
    throw new Error(  "*** Parse.idr:74:14:unmatched case in Parse.case block in parseCharacter at Parse.idr:74:14 ***");
}

// Parse.{parseCharacter_354}

function Parse___123_parseCharacter_95_354_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0((new $JSRTS.jsbn.BigInteger(''+((($_0_lift).length)))), (new $JSRTS.jsbn.BigInteger(("1"))))) {
        let $cg$3 = null;
        if(($_0_lift === "")) {
            $cg$3 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the head of an empty string"));
        } else {
            $cg$3 = $_0_lift[0];
        }
        
        $cg$1 = new $HC_1_9$DataTypes__LispCharacter($cg$3);
    } else {
        
        if(($_0_lift === "altmode")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(27));
        } else if(($_0_lift === "backnext")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(31));
        } else if(($_0_lift === "backspace")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(8));
        } else if(($_0_lift === "call")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(26));
        } else if(($_0_lift === "linefeed")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(10));
        } else if(($_0_lift === "newline")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter("\n");
        } else if(($_0_lift === "page")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(12));
        } else if(($_0_lift === "return")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(13));
        } else if(($_0_lift === "rubout")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(127));
        } else if(($_0_lift === "space")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(" ");
        } else if(($_0_lift === "tab")) {
            $cg$1 = new $HC_1_9$DataTypes__LispCharacter(Prelude__Chars__chr(9));
        } else {
            $cg$1 = new $JSRTS.Lazy((function(){
                return (function(){
                    return Parse___123_parseCharacter_95_353_125_();
                })();
            }));
        }
    }
    
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$1, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseCharacter_355}

function Parse___123_parseCharacter_95_355_125_($_0_lift){
    const $_3_in = Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$Parse___123_parseCharacter_95_352_125_(), $_0_lift));
    return $partial_1_2$Parse___123_parseCharacter_95_354_125_($_3_in);
}

// Parse.{parseCharacter_356}

function Parse___123_parseCharacter_95_356_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many1(null, ParserCombinator__sat($partial_0_1$Parse___123_parseAtom_95_344_125_())), $partial_0_1$Parse___123_parseCharacter_95_355_125_());
}

// ParseNumber.{parseComplexBinary_357}

function ParseNumber___123_parseComplexBinary_95_357_125_($_0_lift){
    return ParseNumber__converterHelper_58_convert_58_0($partial_0_1$ParseNumber__binConverter(), (new $JSRTS.jsbn.BigInteger(("2"))), null, (new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift);
}

// ParseNumber.{parseComplexDecimal_360}

function ParseNumber___123_parseComplexDecimal_95_360_125_($_0_lift){
    return ParseNumber__converterHelper_58_convert_58_0($partial_0_1$ParseNumber__decConverter(), (new $JSRTS.jsbn.BigInteger(("10"))), null, (new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift);
}

// ParseNumber.{parseComplexHelper_363}

function ParseNumber___123_parseComplexHelper_95_363_125_(){
    throw new Error(  "*** ParseNumber.idr:257:9-39:unmatched case in ParseNumber.parseComplexHelper, toDouble ***");
}

// ParseNumber.{parseComplexHelper_364}

function ParseNumber___123_parseComplexHelper_95_364_125_($_0_lift){
    
    if(($_0_lift.type === 5)) {
        return new $HC_1_1$Prelude__Maybe__Just($_0_lift.$1);
    } else if(($_0_lift.type === 4)) {
        return new $HC_1_1$Prelude__Maybe__Just((($_0_lift.$1).intValue()));
    } else if(($_0_lift.type === 7)) {
        return Ratio__rationalCast($_0_lift.$1);
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_parseComplexHelper_95_363_125_();
            })();
        }));
    }
}

// ParseNumber.{parseComplexHelper_366}

function ParseNumber___123_parseComplexHelper_95_366_125_($_0_lift){
    
    if(($_0_lift.type === 5)) {
        return new $HC_1_1$Prelude__Maybe__Just($_0_lift.$1);
    } else if(($_0_lift.type === 4)) {
        return new $HC_1_1$Prelude__Maybe__Just((($_0_lift.$1).intValue()));
    } else if(($_0_lift.type === 7)) {
        return Ratio__rationalCast($_0_lift.$1);
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_parseComplexHelper_95_363_125_();
            })();
        }));
    }
}

// ParseNumber.{parseComplexHelper_367}

function ParseNumber___123_parseComplexHelper_95_367_125_($_0_lift){
    return ($_0_lift === "i");
}

// ParseNumber.{parseComplexHelper_368}

function ParseNumber___123_parseComplexHelper_95_368_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_($_0_lift, $_1_lift)), $_2_lift), $HC_0_0$Prelude__List__Nil));
}

// ParseNumber.{parseComplexHelper_369}

function ParseNumber___123_parseComplexHelper_95_369_125_($_0_lift, $_1_lift, $_2_lift){
    
    if(($_0_lift.type === 1)) {
        
        if(($_1_lift.type === 1)) {
            return $partial_2_3$ParseNumber___123_parseComplexHelper_95_368_125_($_0_lift.$1, $_1_lift.$1);
        } else {
            return $partial_2_3$ParserCombinator__failure(null, "Division by zero");
        }
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Division by zero");
    }
}

// ParseNumber.{parseComplexHelper_370}

function ParseNumber___123_parseComplexHelper_95_370_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseComplexHelper_95_367_125_()), $partial_2_3$ParseNumber___123_parseComplexHelper_95_369_125_($_0_lift, $_1_lift));
}

// ParseNumber.{parseComplexHelper_371}

function ParseNumber___123_parseComplexHelper_95_371_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(null, null, $partial_0_1$ParseNumber___123_parseComplexHelper_95_366_125_(), $partial_3_4$ParserCombinator___60__124__62_(null, $_0_lift, $partial_3_4$ParserCombinator___60__124__62_(null, $_1_lift, $_2_lift))), $partial_1_2$ParseNumber___123_parseComplexHelper_95_370_125_($_3_lift));
}

// ParseNumber.{parseComplexHex_372}

function ParseNumber___123_parseComplexHex_95_372_125_($_0_lift){
    return ParseNumber__converterHelper_58_convert_58_0($partial_0_1$ParseNumber__hexConverter(), (new $JSRTS.jsbn.BigInteger(("16"))), null, (new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift);
}

// ParseNumber.{parseComplexOctal_375}

function ParseNumber___123_parseComplexOctal_95_375_125_($_0_lift){
    return ParseNumber__converterHelper_58_convert_58_0($partial_0_1$ParseNumber__octConverter(), (new $JSRTS.jsbn.BigInteger(("8"))), null, (new $JSRTS.jsbn.BigInteger(("0"))), $_0_lift);
}

// Parse.{parseDottedList_378}

function Parse___123_parseDottedList_95_378_125_($_0_lift){
    return ($_0_lift === ".");
}

// Parse.{parseDottedList_381}

function Parse___123_parseDottedList_95_381_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_0_lift.type === 3)) {
        return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_2_3$DataTypes__LispDottedList(Prelude__List___43__43_(null, $_1_lift, $_0_lift.$1), new $JSRTS.Lazy((function(){
            return (function(){
                return Lists___123_cdr_95_12_125_($_0_lift.$2);
            })();
        }))), $_3_lift), $HC_0_0$Prelude__List__Nil));
    } else if(($_0_lift.type === 2)) {
        return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_2$DataTypes__LispList(Prelude__List___43__43_(null, $_1_lift, $_0_lift.$1)), $_3_lift), $HC_0_0$Prelude__List__Nil));
    } else {
        return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_2_3$DataTypes__LispDottedList($_1_lift, new $JSRTS.Lazy((function(){
            return (function(){
                return Lists___123_cons_95_14_125_($_0_lift);
            })();
        }))), $_3_lift), $HC_0_0$Prelude__List__Nil));
    }
}

// Parse.{parseDottedList_382}

function Parse___123_parseDottedList_95_382_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_2_4$Parse___123_parseDottedList_95_381_125_($_1_lift, $_0_lift));
}

// Parse.{parseDottedList_383}

function Parse___123_parseDottedList_95_383_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__parseExpr(), $partial_1_2$Parse___123_parseDottedList_95_382_125_($_0_lift));
}

// Parse.{parseDottedList_384}

function Parse___123_parseDottedList_95_384_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())), $partial_1_2$Parse___123_parseDottedList_95_383_125_($_0_lift));
}

// Parse.{parseDottedList_385}

function Parse___123_parseDottedList_95_385_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseDottedList_95_378_125_()), $partial_1_2$Parse___123_parseDottedList_95_384_125_($_0_lift));
}

// Parse.{parseDottedList_386}

function Parse___123_parseDottedList_95_386_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__endBy(null, null, Parse__parseExpr(), ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseDottedList_95_385_125_());
}

// ParseNumber.{parseFloat_388}

function ParseNumber___123_parseFloat_95_388_125_($_0_lift){
    return ($_0_lift === "#");
}

// ParseNumber.{parseFloat_389}

function ParseNumber___123_parseFloat_95_389_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__oneOf("bdox"), $partial_0_1$ParseNumber__parseFloatBase());
}

// ParseNumber.{parseFloatHelper_394}

function ParseNumber___123_parseFloatHelper_95_394_125_($_0_lift){
    return ($_0_lift === "-");
}

// ParseNumber.{parseFloatHelper_395}

function ParseNumber___123_parseFloatHelper_95_395_125_($_0_lift){
    return (-($_0_lift));
}

// ParseNumber.{parseFloatHelper_396}

function ParseNumber___123_parseFloatHelper_95_396_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return ParseNumber__parseFloatHelper_58_parseFloat_39__58_0($_0_lift, $_1_lift, $_2_lift, $partial_0_1$ParseNumber___123_parseFloatHelper_95_395_125_());
}

// ParseNumber.{parseFloatHelper_397}

function ParseNumber___123_parseFloatHelper_95_397_125_($_0_lift){
    return ($_0_lift === "+");
}

// ParseNumber.{parseFloatHelper_399}

function ParseNumber___123_parseFloatHelper_95_399_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return ParseNumber__parseFloatHelper_58_parseFloat_39__58_0($_0_lift, $_1_lift, $_2_lift, $partial_0_1$Lists___123_cons_95_14_125_());
}

// ParseNumber.{parseInteger_403}

function ParseNumber___123_parseInteger_95_403_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__oneOf("bdox"), $partial_0_1$ParseNumber__parseIntegerBase());
}

// ParseNumber.{parseIntegerHelper_409}

function ParseNumber___123_parseIntegerHelper_95_409_125_($_0_lift){
    return (new $JSRTS.jsbn.BigInteger(("0"))).subtract($_0_lift);
}

// ParseNumber.{parseIntegerHelper_410}

function ParseNumber___123_parseIntegerHelper_95_410_125_($_0_lift, $_1_lift, $_2_lift){
    return ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0($_0_lift, $_1_lift, $partial_0_1$ParseNumber___123_parseIntegerHelper_95_409_125_());
}

// ParseNumber.{parseIntegerHelper_413}

function ParseNumber___123_parseIntegerHelper_95_413_125_($_0_lift, $_1_lift, $_2_lift){
    return ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0($_0_lift, $_1_lift, $partial_0_1$Lists___123_cons_95_14_125_());
}

// Parse.{parseLineComment_415}

function Parse___123_parseLineComment_95_415_125_($_0_lift){
    return ($_0_lift === ";");
}

// Parse.{parseLineComment_416}

function Parse___123_parseLineComment_95_416_125_($_0_lift){
    return ($_0_lift === "\n");
}

// Parse.{parseLineComment_418}

function Parse___123_parseLineComment_95_418_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipUntil_58_scan_58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseLineComment_95_416_125_()), $partial_0_1$ParserCombinator__item()), $partial_0_2$Parse___123_parseBlockComment_95_349_125_());
}

// Parse.{parseList_419}

function Parse___123_parseList_95_419_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_2$DataTypes__LispList($_0_lift), $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// ParseNumber.{parseNumber_421}

function ParseNumber___123_parseNumber_95_421_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__oneOf("bdox"), $partial_0_1$ParseNumber__parseComplexBase());
}

// Parse.{parseQuoted_422}

function Parse___123_parseQuoted_95_422_125_($_0_lift){
    return ($_0_lift === "\'");
}

// Parse.{parseQuoted_423}

function Parse___123_parseQuoted_95_423_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_(new $HC_1_1$DataTypes__LispAtom("quote"), new $HC_2_1$Prelude__List___58__58_($_0_lift, $HC_0_0$Prelude__List__Nil))), $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseQuoted_424}

function Parse___123_parseQuoted_95_424_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__parseExpr(), $partial_0_2$Parse___123_parseQuoted_95_423_125_());
}

// ParseNumber.{parseRational_427}

function ParseNumber___123_parseRational_95_427_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__oneOf("bdox"), $partial_0_1$ParseNumber__parseRationalBase());
}

// ParseNumber.{parseRationalHelper_432}

function ParseNumber___123_parseRationalHelper_95_432_125_(){
    throw new Error(  "*** ParseNumber.idr:213:9-33:unmatched case in ParseNumber.parseRationalHelper, toInt ***");
}

// ParseNumber.{parseRationalHelper_433}

function ParseNumber___123_parseRationalHelper_95_433_125_($_0_lift){
    
    if(($_0_lift.type === 4)) {
        return $_0_lift.$1;
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_parseRationalHelper_95_432_125_();
            })();
        }));
    }
}

// ParseNumber.{parseRationalHelper_434}

function ParseNumber___123_parseRationalHelper_95_434_125_($_0_lift){
    return ($_0_lift === "/");
}

// ParseNumber.{parseRationalHelper_436}

function ParseNumber___123_parseRationalHelper_95_436_125_($_0_lift){
    
    if(($_0_lift.type === 4)) {
        return $_0_lift.$1;
    } else {
        return new $JSRTS.Lazy((function(){
            return (function(){
                return ParseNumber___123_parseRationalHelper_95_432_125_();
            })();
        }));
    }
}

// ParseNumber.{parseRationalHelper_454}

function ParseNumber___123_parseRationalHelper_95_454_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_7$DataTypes__LispRational($_0_lift), $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// ParseNumber.{parseRationalHelper_455}

function ParseNumber___123_parseRationalHelper_95_455_125_($_0_lift, $_1_lift){
    const $_53_in = Ratio___58__37_(null, new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), $_0_lift, $_1_lift);
    
    if(($_53_in.type === 1)) {
        return $partial_1_2$ParseNumber___123_parseRationalHelper_95_454_125_($_53_in.$1);
    } else {
        return $partial_2_3$ParserCombinator__failure(null, "Division by zero");
    }
}

// ParseNumber.{parseRationalHelper_456}

function ParseNumber___123_parseRationalHelper_95_456_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(null, null, $partial_0_1$ParseNumber___123_parseRationalHelper_95_436_125_(), $_0_lift), $partial_1_2$ParseNumber___123_parseRationalHelper_95_455_125_($_1_lift));
}

// ParseNumber.{parseRationalHelper_457}

function ParseNumber___123_parseRationalHelper_95_457_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$ParseNumber___123_parseRationalHelper_95_434_125_()), $partial_2_3$ParseNumber___123_parseRationalHelper_95_456_125_($_0_lift, $_1_lift));
}

// Parse.{parseRawList_459}

function Parse___123_parseRawList_95_459_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_1_3$Parse___123_bracketed_95_9_125_($_0_lift));
}

// Parse.{parseRawList_460}

function Parse___123_parseRawList_95_460_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sepBy(null, null, Parse__parseExpr(), ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseRawList_95_459_125_());
}

// Parse.{parseString_461}

function Parse___123_parseString_95_461_125_($_0_lift){
    return ($_0_lift === "\"");
}

// Parse.{parseString_464}

function Parse___123_parseString_95_464_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_8$DataTypes__LispString(Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_2$prim_95__95_strCons(), "", $_0_lift)), $_2_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseString_465}

function Parse___123_parseString_95_465_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseString_95_461_125_()), $partial_1_3$Parse___123_parseString_95_464_125_($_0_lift));
}

// Parse.{parseString_466}

function Parse___123_parseString_95_466_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many_39_(null, $partial_3_4$ParserCombinator___60__124__62_(null, Parse__parseString_58_escapedChar_58_0(), ParserCombinator__rej($partial_0_1$Parse___123_parseString_95_461_125_()))), $partial_0_1$Parse___123_parseString_95_465_125_());
}

// Parse.{parseTwoDot_469}

function Parse___123_parseTwoDot_95_469_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_0_lift, Prelude__List___43__43_(null, $_1_lift, $_2_lift))), $_3_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseTwoDot_470}

function Parse___123_parseTwoDot_95_470_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_0_lift.type === 0)) {
        return $partial_2_3$ParserCombinator__failure(null, "Illegal use of `.`");
    } else {
        
        if(($_1_lift.type === 0)) {
            return $partial_2_3$ParserCombinator__failure(null, "Illegal use of `.`");
        } else {
            return $partial_3_4$Parse___123_parseTwoDot_95_469_125_($_2_lift, $_0_lift, $_1_lift);
        }
    }
}

// Parse.{parseTwoDot_471}

function Parse___123_parseTwoDot_95_471_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany(null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_3_4$Parse___123_parseTwoDot_95_470_125_($_0_lift, $_2_lift, $_1_lift));
}

// Parse.{parseTwoDot_472}

function Parse___123_parseTwoDot_95_472_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sepBy(null, null, Parse__parseExpr(), ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_2_3$Parse___123_parseTwoDot_95_471_125_($_0_lift, $_1_lift));
}

// Parse.{parseTwoDot_473}

function Parse___123_parseTwoDot_95_473_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())), $partial_2_3$Parse___123_parseTwoDot_95_472_125_($_0_lift, $_1_lift));
}

// Parse.{parseTwoDot_474}

function Parse___123_parseTwoDot_95_474_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseDottedList_95_378_125_()), $partial_2_3$Parse___123_parseTwoDot_95_473_125_($_0_lift, $_1_lift));
}

// Parse.{parseTwoDot_475}

function Parse___123_parseTwoDot_95_475_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())), $partial_2_3$Parse___123_parseTwoDot_95_474_125_($_0_lift, $_1_lift));
}

// Parse.{parseTwoDot_476}

function Parse___123_parseTwoDot_95_476_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__parseExpr(), $partial_1_2$Parse___123_parseTwoDot_95_475_125_($_0_lift));
}

// Parse.{parseTwoDot_477}

function Parse___123_parseTwoDot_95_477_125_($_0_lift, $_1_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())), $partial_1_2$Parse___123_parseTwoDot_95_476_125_($_0_lift));
}

// Parse.{parseTwoDot_478}

function Parse___123_parseTwoDot_95_478_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseDottedList_95_378_125_()), $partial_1_2$Parse___123_parseTwoDot_95_477_125_($_0_lift));
}

// Parse.{parseTwoDot_479}

function Parse___123_parseTwoDot_95_479_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__endBy(null, null, Parse__parseExpr(), ParserCombinator__skipMany1(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace()))), $partial_0_1$Parse___123_parseTwoDot_95_478_125_());
}

// Parse.{parseVector_481}

function Parse___123_parseVector_95_481_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_2_0$DataTypes__LispVector(((Prelude__List__length(null, $_0_lift)).intValue()|0), $_0_lift), $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Parse.{parseVector_482}

function Parse___123_parseVector_95_482_125_($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, Parse__bracketed(null, Parse__parseRawList()), $partial_0_2$Parse___123_parseVector_95_481_125_());
}

// Eval.{primitiveBindings_483}

function Eval___123_primitiveBindings_95_483_125_($_0_lift){
    
    return new $HC_2_0$Builtins__MkPair($_0_lift.$1, new $HC_1_11$DataTypes__LispPrimitiveFunc($_0_lift.$2));
}

// Primitives.{primitives_484}

function Primitives___123_primitives_95_484_125_($_0_lift){
    return new $HC_1_1$Prelude__Either__Right($HC_0_13$DataTypes__LispVoid);
}

// Repl.{readExprList_485}

function Repl___123_readExprList_95_485_125_($_0_lift){
    return ParserCombinator__endBy(null, null, Parse__parseExpr(), ParserCombinator__skipMany(null, ParserCombinator__sat($partial_0_1$Prelude__Chars__isSpace())));
}

// ParserCombinator.{rej_486}

function ParserCombinator___123_rej_95_486_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_0_lift, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// ParserCombinator.{rej_487}

function ParserCombinator___123_rej_95_487_125_($_0_lift, $_1_lift){
    
    if($_0_lift($_1_lift)) {
        return $partial_2_3$ParserCombinator__failure(null, ("Rejection condition not satisfied for: `" + ((($_1_lift)+("")) + "`")));
    } else {
        return $partial_1_2$ParserCombinator___123_rej_95_486_125_($_1_lift);
    }
}

// Main.{replEval_488}

function Main___123_replEval_95_488_125_($_0_lift, $_1_lift, $_2_lift){
    return Control__ST__Exception__Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0(null, null, null, $_2_lift);
}

// Main.{replEval_489}

function Main___123_replEval_95_489_125_($_0_lift, $_1_lift){
    return Control__ST__Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0(null, null, $_1_lift);
}

// Main.{replEval_490}

function Main___123_replEval_95_490_125_($_0_lift, $_1_lift){
    return $partial_2_3$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_newIORef_39__58_0(null, $_1_lift);
}

// Main.{replEval_491}

function Main___123_replEval_95_491_125_($_0_lift, $_1_lift){
    return $partial_2_3$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_readIORef_39__58_0(null, $_1_lift);
}

// Main.{replEval_492}

function Main___123_replEval_95_492_125_($_0_lift, $_1_lift, $_2_lift){
    return $partial_3_4$Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_writeIORef_39__58_0(null, $_1_lift, $_2_lift);
}

// Main.{replEval_493}

function Main___123_replEval_95_493_125_($_0_lift, $_1_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_showEnv_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift, $_1_lift);
}

// Main.{replEval_497}

function Main___123_replEval_95_497_125_($_0_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_initEnv_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift);
}

// Main.{replEval_501}

function Main___123_replEval_95_501_125_($_0_lift, $_1_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_getVar_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift, $_1_lift);
}

// Main.{replEval_505}

function Main___123_replEval_95_505_125_($_0_lift, $_1_lift, $_2_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_setVar_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift, $_1_lift, $_2_lift);
}

// Main.{replEval_509}

function Main___123_replEval_95_509_125_($_0_lift, $_1_lift, $_2_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_defineVar_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift, $_1_lift, $_2_lift);
}

// Main.{replEval_513}

function Main___123_replEval_95_513_125_($_0_lift, $_1_lift){
    return Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_bindVars_58_0(null, null, null, new $HC_3_0$Data__IORef__HasReference_95_ictor($partial_0_2$Main___123_replEval_95_490_125_(), $partial_0_2$Main___123_replEval_95_491_125_(), $partial_0_3$Main___123_replEval_95_492_125_()), $_0_lift, $_1_lift);
}

// Main.{replEval_540}

function Main___123_replEval_95_540_125_($_0_lift){
    return (!($_0_lift.type === 13));
}

// Main.{replEval_541}

function Main___123_replEval_95_541_125_($_0_lift){
    return new $HC_1_0$Control__ST__Pure(Prelude__Strings__unlines(Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $partial_0_1$DataTypes__showVal(), Prelude__List__filter(null, $partial_0_1$Main___123_replEval_95_540_125_(), $_0_lift))));
}

// Main.{replEval_542}

function Main___123_replEval_95_542_125_($_0_lift, $_1_lift){
    return new $HC_2_1$Control__ST__Bind(Repl__evalExprList(null, new $HC_3_0$DataTypes__Context_95_ictor($partial_0_3$Main___123_replEval_95_488_125_(), $partial_0_2$Main___123_replEval_95_489_125_(), new $HC_6_0$Environment__Envir_95_ictor($partial_0_2$Main___123_replEval_95_493_125_(), $partial_0_1$Main___123_replEval_95_497_125_(), $partial_0_2$Main___123_replEval_95_501_125_(), $partial_0_3$Main___123_replEval_95_505_125_(), $partial_0_3$Main___123_replEval_95_509_125_(), $partial_0_2$Main___123_replEval_95_513_125_())), $_1_lift, $_0_lift), $partial_0_1$Main___123_replEval_95_541_125_());
}

// Main.{replEval_543}

function Main___123_replEval_95_543_125_($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_1$Prelude__Either__Right($_0_lift);
}

// Main.{replEval_544}

function Main___123_replEval_95_544_125_($_0_lift, $_1_lift){
    return DataTypes__showError($_0_lift);
}

// Main.{replEval_545}

function Main___123_replEval_95_545_125_($_0_lift, $_1_lift){
    return $_0_lift;
}

// Control.ST.{runST_546}

function Control__ST___123_runST_95_546_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Control__ST__runST(null, null, null, null, null, $_3_lift, $_0_lift($_2_lift), $_1_lift);
}

// Control.ST.{runST_547}

function Control__ST___123_runST_95_547_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $_0_lift($_3_lift)(Control__ST__rebuildEnv(null, null, null, $_4_lift, $_1_lift, $_2_lift));
}

// Control.ST.{runST_548}

function Control__ST___123_runST_95_548_125_($_0_lift, $_1_lift, $_2_lift){
    return $_0_lift($_2_lift)($_1_lift);
}

// ParserCombinator.{sat_551}

function ParserCombinator___123_sat_95_551_125_($_0_lift, $_1_lift){
    
    if($_0_lift($_1_lift)) {
        return $partial_1_2$ParserCombinator___123_rej_95_486_125_($_1_lift);
    } else {
        return $partial_2_3$ParserCombinator__failure(null, ("Condition not satisfied for: `" + ((($_1_lift)+("")) + "`")));
    }
}

// Prelude.Show.{showLitChar_553}

function Prelude__Show___123_showLitChar_95_553_125_($_0_lift){
    return ("\\a" + $_0_lift);
}

// Prelude.Show.{showLitChar_554}

function Prelude__Show___123_showLitChar_95_554_125_($_0_lift){
    return ("\\b" + $_0_lift);
}

// Prelude.Show.{showLitChar_555}

function Prelude__Show___123_showLitChar_95_555_125_($_0_lift){
    return ("\\t" + $_0_lift);
}

// Prelude.Show.{showLitChar_556}

function Prelude__Show___123_showLitChar_95_556_125_($_0_lift){
    return ("\\n" + $_0_lift);
}

// Prelude.Show.{showLitChar_557}

function Prelude__Show___123_showLitChar_95_557_125_($_0_lift){
    return ("\\v" + $_0_lift);
}

// Prelude.Show.{showLitChar_558}

function Prelude__Show___123_showLitChar_95_558_125_($_0_lift){
    return ("\\f" + $_0_lift);
}

// Prelude.Show.{showLitChar_559}

function Prelude__Show___123_showLitChar_95_559_125_($_0_lift){
    return ("\\r" + $_0_lift);
}

// Prelude.Show.{showLitChar_560}

function Prelude__Show___123_showLitChar_95_560_125_($_0_lift){
    return ($_0_lift === "H");
}

// Prelude.Show.{showLitChar_561}

function Prelude__Show___123_showLitChar_95_561_125_($_0_lift){
    return ("\\\\" + $_0_lift);
}

// Prelude.Show.{showLitChar_562}

function Prelude__Show___123_showLitChar_95_562_125_($_0_lift){
    return ("\\DEL" + $_0_lift);
}

// Prelude.Show.{showLitChar_563}

function Prelude__Show___123_showLitChar_95_563_125_($_0_lift, $_1_lift){
    return prim_95__95_strCons("\\", ($_0_lift + $_1_lift));
}

// Prelude.Show.{showLitChar_564}

function Prelude__Show___123_showLitChar_95_564_125_($_0_lift, $_1_lift){
    return prim_95__95_strCons("\\", Prelude__Show__protectEsc($partial_0_1$Prelude__Chars__isDigit(), Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_toStrInt(), $HC_0_0$Prelude__Show__Open, (($_0_lift).charCodeAt(0)|0)), $_1_lift));
}

// DataTypes.{showVal_565}

function DataTypes___123_showVal_95_565_125_($_0_lift){
    return Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_floatToStr(), $HC_0_0$Prelude__Show__Open, $_0_lift);
}

// DataTypes.{showVal_566}

function DataTypes___123_showVal_95_566_125_($_0_lift, $_1_lift){
    return Prelude__Show__primNumShow(null, $partial_0_1$prim_95__95_floatToStr(), $_0_lift, $_1_lift);
}

// ParserCombinator.{skipMany_567}

function ParserCombinator___123_skipMany_95_567_125_($_0_lift, $_1_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($HC_0_0$MkUnit, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// Strings.{strPrimitives_570}

function Strings___123_strPrimitives_95_570_125_($_0_lift, $_1_lift){
    return (!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) < 0)));
}

// Strings.{strPrimitives_571}

function Strings___123_strPrimitives_95_571_125_($_0_lift, $_1_lift){
    return (!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) > 0)));
}

// Strings.{strPrimitives_573}

function Strings___123_strPrimitives_95_573_125_($_0_lift, $_1_lift){
    
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_lift, $_1_lift) > 0)) {
        return true;
    } else {
        return ($_0_lift == $_1_lift);
    }
}

// ParserCombinator.{string_574}

function ParserCombinator___123_string_95_574_125_($_0_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair("", $_0_lift), $HC_0_0$Prelude__List__Nil));
}

// ParserCombinator.{string_577}

function ParserCombinator___123_string_95_577_125_($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift === "")) {
        $cg$1 = $JSRTS.throw(new Error(  "Prelude.Strings: attempt to take the tail of an empty string"));
    } else {
        $cg$1 = $_0_lift.slice(1);
    }
    
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__string($cg$1), $partial_1_3$Parse___123_bracketed_95_9_125_($_0_lift));
}

// Strings.{substring_578}

function Strings___123_substring_95_578_125_(){
    throw new Error(  "*** Strings.idr:58:1-64:73:unmatched case in Strings.substring ***");
}

// Data.SortedMap.{toList_585}

function Data__SortedMap___123_toList_95_585_125_($_0_lift){
    return new $HC_2_1$Prelude__List___58__58_($_0_lift, $HC_0_0$Prelude__List__Nil);
}

// Prelude.Strings.{unlines_586}

function Prelude__Strings___123_unlines_95_586_125_($_0_lift){
    let $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    
    if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true).type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$3 = null;
        if((((($_0_lift.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        let $cg$4 = null;
        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true).type === 1)) {
            $cg$4 = $HC_0_0$Prelude__List__Nil;
        } else {
            let $cg$5 = null;
            if((((($_0_lift.slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                $cg$5 = true;
            } else {
                $cg$5 = false;
            }
            
            let $cg$6 = null;
            if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$5, true).type === 1)) {
                $cg$6 = $HC_0_0$Prelude__List__Nil;
            } else {
                let $cg$7 = null;
                if((((($_0_lift.slice(1).slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                    $cg$7 = true;
                } else {
                    $cg$7 = false;
                }
                
                let $cg$8 = null;
                if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$7, true).type === 1)) {
                    $cg$8 = $HC_0_0$Prelude__List__Nil;
                } else {
                    $cg$8 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1).slice(1).slice(1)[0], Prelude__Strings__unpack($_0_lift.slice(1).slice(1).slice(1).slice(1)));
                }
                
                $cg$6 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1).slice(1)[0], $cg$8);
            }
            
            $cg$4 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1)[0], $cg$6);
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_0_lift[0], $cg$4);
    }
}

// Prelude.Strings.{unwords_587}

function Prelude__Strings___123_unwords_95_587_125_($_0_lift){
    let $cg$1 = null;
    if((((($_0_lift == "")) ? 1|0 : 0|0) === 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = false;
    }
    
    
    if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$1, true).type === 1)) {
        return $HC_0_0$Prelude__List__Nil;
    } else {
        let $cg$3 = null;
        if((((($_0_lift.slice(1) == "")) ? 1|0 : 0|0) === 0)) {
            $cg$3 = true;
        } else {
            $cg$3 = false;
        }
        
        let $cg$4 = null;
        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$3, true).type === 1)) {
            $cg$4 = $HC_0_0$Prelude__List__Nil;
        } else {
            let $cg$5 = null;
            if((((($_0_lift.slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                $cg$5 = true;
            } else {
                $cg$5 = false;
            }
            
            let $cg$6 = null;
            if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$5, true).type === 1)) {
                $cg$6 = $HC_0_0$Prelude__List__Nil;
            } else {
                let $cg$7 = null;
                if((((($_0_lift.slice(1).slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                    $cg$7 = true;
                } else {
                    $cg$7 = false;
                }
                
                let $cg$8 = null;
                if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$7, true).type === 1)) {
                    $cg$8 = $HC_0_0$Prelude__List__Nil;
                } else {
                    let $cg$9 = null;
                    if((((($_0_lift.slice(1).slice(1).slice(1).slice(1) == "")) ? 1|0 : 0|0) === 0)) {
                        $cg$9 = true;
                    } else {
                        $cg$9 = false;
                    }
                    
                    let $cg$10 = null;
                    if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$9, true).type === 1)) {
                        $cg$10 = $HC_0_0$Prelude__List__Nil;
                    } else {
                        $cg$10 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1).slice(1).slice(1).slice(1)[0], Prelude__Strings__unpack($_0_lift.slice(1).slice(1).slice(1).slice(1).slice(1)));
                    }
                    
                    $cg$8 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1).slice(1).slice(1)[0], $cg$10);
                }
                
                $cg$6 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1).slice(1)[0], $cg$8);
            }
            
            $cg$4 = new $HC_2_1$Prelude__List___58__58_($_0_lift.slice(1)[0], $cg$6);
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_0_lift[0], $cg$4);
    }
}

// Prelude.Strings.{unwords_588}

function Prelude__Strings___123_unwords_95_588_125_($_0_lift, $_1_lift){
    return Prelude__List___43__43_(null, $_0_lift, new $HC_2_1$Prelude__List___58__58_(" ", $_1_lift));
}

// Control.ST.{Util.@Control.ST.ConsoleIO$IOExcept' FFI_JS err:!putStr:0_lam_695}

function Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Monad__Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0(null, null, null, null, $_2_lift, $_3_lift);
}

// Control.ST.{Util.@Control.ST.ConsoleIO$IOExcept' FFI_JS err:!putStr:0_lam_696}

function Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_696_125_($_0_lift, $_1_lift){
    const $_8_in = $JSRTS.prim_writeStr(($_0_lift + "\n"));
    return $HC_0_0$MkUnit;
}

// Control.ST.Exception.{Util.@Control.ST.Exception.Exception$IOExcept' FFI_JS err:err:!throw:0_lam_705}

function Control__ST__Exception___123_Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0_95_lam_95_705_125_($_0_lift, $_1_lift){
    return new $HC_1_0$Prelude__Either__Left($_0_lift);
}

// Prelude.Monad.{Control.IOExcept.@Prelude.Monad.Monad$IOExcept' f e:!>>=:0_lam_707}

function Prelude__Monad___123_Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0_95_lam_95_707_125_($_0_lift, $_1_lift){
    
    if(($_1_lift.type === 0)) {
        return $partial_1_2$Control__ST__Exception___123_Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0_95_lam_95_705_125_($_1_lift.$1);
    } else {
        return $_0_lift($_1_lift.$1);
    }
}

// Control.ST.Util.IOExcept' FFI_JS err implementation of Control.ST.ConsoleIO, method putStr

function Control__ST__Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0($_0_arg, $_1_arg, $_2_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_1_2$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_696_125_($_2_arg)));
}

// Decidable.Equality.Decidable.Equality.Bool implementation of Decidable.Equality.DecEq, method decEq

function Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($_0_arg, $_1_arg){
    
    if($_1_arg) {
        
        if($_0_arg) {
            return $HC_0_0$Prelude__Basics__Yes;
        } else {
            return $HC_0_1$Prelude__Basics__No;
        }
    } else {
        
        if($_0_arg) {
            return $HC_0_1$Prelude__Basics__No;
        } else {
            return $HC_0_0$Prelude__Basics__Yes;
        }
    }
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method bindVars

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_bindVars_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_5_6$Util__bindVars_39__58_bindHelper_58_0(null, null, $_4_arg, $_5_arg, $_3_arg)));
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method defineVar

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_defineVar_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_7_8$Util__defineVar_39__58_defineHelper_58_0(null, null, null, $_5_arg, $_6_arg, $_3_arg, $_4_arg)));
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method getVar

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_getVar_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_6_7$Util__getVar_39__58_getHelper_58_0(null, null, null, $_5_arg, $_3_arg, $_4_arg)));
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method initEnv

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_initEnv_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_4_5$Util__initEnv_39_(null, null, $_3_arg, $_4_arg)));
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method setVar

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_setVar_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_7_8$Util__setVar_39__58_setHelper_58_0(null, null, null, $_5_arg, $_6_arg, $_3_arg, $_4_arg)));
}

// Environment.Util.a, IOExcept' ffi err implementation of Environment.Envir, method showEnv

function Environment__Util___64_Environment__Envir_36_a_58_IOExcept_39__32_ffi_32_err_58__33_showEnv_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_4_5$Control__IOExcept__ioe_95_lift(null, null, null, $partial_6_7$Util__showEnv_39__58_printEnv_58_0(null, null, null, $_4_arg, $_3_arg, $_5_arg)));
}

// Prelude.Interfaces.Prelude.Interfaces.Bool implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Eq_36_Bool_58__33__61__61__58_0($_0_arg, $_1_arg){
    
    if($_1_arg) {
        
        if($_0_arg) {
            return $_0_arg;
        } else {
            return $_0_arg;
        }
    } else {
        return (!(!(!$_0_arg)));
    }
}

// Prelude.Interfaces.Data.Complex.Complex a implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    let $cg$1 = null;
    $cg$1 = $_2_arg.$1;
    let $cg$2 = null;
    $cg$2 = $_3_arg.$1;
    
    if($_1_arg($cg$1)($cg$2)) {
        let $cg$4 = null;
        $cg$4 = $_2_arg.$2;
        let $cg$5 = null;
        $cg$5 = $_3_arg.$2;
        return $_1_arg($cg$4)($cg$5);
    } else {
        return false;
    }
}

// Prelude.Interfaces.DataTypes.LispVal implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__DataTypes___64_Prelude__Interfaces__Eq_36_LispVal_58__33__61__61__58_0($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        
        if(($_0_arg.type === 1)) {
            return ($_0_arg.$1 == $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 10)) {
        
        if(($_0_arg.type === 10)) {
            return Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Eq_36_Bool_58__33__61__61__58_0($_0_arg.$1, $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 9)) {
        
        if(($_0_arg.type === 9)) {
            return ($_0_arg.$1 === $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 6)) {
        
        if(($_0_arg.type === 6)) {
            return Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0(null, $partial_0_2$Primitives___123_eqv_95_22_125_(), $_0_arg.$1, $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 3)) {
        
        if(($_0_arg.type === 3)) {
            
            if(Prelude__Interfaces__DataTypes___64_Prelude__Interfaces__Eq_36_LispVal_58__33__61__61__58_0($JSRTS.force($_0_arg.$2), $JSRTS.force($_1_arg.$2))) {
                return false;
            } else {
                return DataTypes__listEq($_0_arg.$1, $_1_arg.$1);
            }
        } else {
            return false;
        }
    } else if(($_1_arg.type === 5)) {
        
        if(($_0_arg.type === 5)) {
            return ($_0_arg.$1 === $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 4)) {
        
        if(($_0_arg.type === 4)) {
            return $_0_arg.$1.equals($_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 2)) {
        
        if(($_0_arg.type === 2)) {
            return DataTypes__listEq($_0_arg.$1, $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 7)) {
        
        if(($_0_arg.type === 7)) {
            const $cg$7 = $_1_arg.$1;
            const $cg$9 = $_0_arg.$1;
            const $cg$11 = $cg$7.$1;
            let $cg$10 = null;
            const $cg$13 = $cg$11.$1;
            $cg$10 = $cg$13.$2($cg$9.$6)($cg$7.$7);
            const $cg$15 = $cg$7.$1;
            let $cg$14 = null;
            const $cg$17 = $cg$15.$1;
            $cg$14 = $cg$17.$2($cg$7.$6)($cg$9.$7);
            return $cg$7.$2($cg$10)($cg$14);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 8)) {
        
        if(($_0_arg.type === 8)) {
            return ($_0_arg.$1 == $_1_arg.$1);
        } else {
            return false;
        }
    } else if(($_1_arg.type === 0)) {
        
        if(($_0_arg.type === 0)) {
            
            if((((($_0_arg.$1 === $_1_arg.$1)) ? 1|0 : 0|0) === 0)) {
                return DataTypes__listEq($_0_arg.$2, $_1_arg.$2);
            } else {
                return false;
            }
        } else {
            return false;
        }
    } else if(($_1_arg.type === 13)) {
        return (!(!($_0_arg.type === 13)));
    } else {
        return false;
    }
}

// Prelude.Interfaces.Prelude.Nat.Nat implementation of Prelude.Interfaces.Eq, method ==

function Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($_0_arg, $_1_arg){
    for(;;) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return true;
            } else {
                return false;
            }
        } else {
            const $_2_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return false;
            } else {
                const $_3_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = $_3_in;
                $_1_arg = $_2_in;
            }
        }
    }
}

// Control.ST.Exception.Util.IOExcept' FFI_JS err, err implementation of Control.ST.Exception.Exception, method throw

function Control__ST__Exception__Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return new $HC_2_2$Control__ST__Lift($partial_0_4$Control__ST___123_Util___64_Control__ST__ConsoleIO_36_IOExcept_39__32_FFI_95_JS_32_err_58__33_putStr_58_0_95_lam_95_695_125_(), $partial_1_2$Control__ST__Exception___123_Util___64_Control__ST__Exception__Exception_36_IOExcept_39__32_FFI_95_JS_32_err_58_err_58__33_throw_58_0_95_lam_95_705_125_($_3_arg));
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldl

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldl_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    let $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_4_arg.type === 1)) {
            $tco$$_3_arg = $_2_arg($_3_arg)($_4_arg.$1);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = $_2_arg;
            $_3_arg = $tco$$_3_arg;
            $_4_arg = $_4_arg.$2;
        } else {
            return $_3_arg;
        }
    }
}

// Prelude.Foldable.Prelude.List.List implementation of Prelude.Foldable.Foldable, method foldr

function Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        return $_2_arg($_4_arg.$1)(Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $_2_arg, $_3_arg, $_4_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Interfaces.Data.Complex.Complex a implementation of Prelude.Interfaces.Fractional, method /

function Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Fractional_36_Complex_32_a_58__33__47__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    
    let $cg$3 = null;
    let $cg$4 = null;
    const $cg$6 = $_2_arg.$1;
    let $cg$7 = null;
    const $cg$9 = $_2_arg.$1;
    $cg$7 = $cg$9.$2($_3_arg.$1)($_4_arg.$1);
    let $cg$10 = null;
    const $cg$12 = $_2_arg.$1;
    $cg$10 = $cg$12.$2($_3_arg.$2)($_4_arg.$2);
    $cg$4 = $cg$6.$1($cg$7)($cg$10);
    let $cg$13 = null;
    const $cg$15 = $_2_arg.$1;
    let $cg$16 = null;
    const $cg$18 = $_2_arg.$1;
    $cg$16 = $cg$18.$2($_4_arg.$1)($_4_arg.$1);
    let $cg$19 = null;
    const $cg$21 = $_2_arg.$1;
    $cg$19 = $cg$21.$2($_4_arg.$2)($_4_arg.$2);
    $cg$13 = $cg$15.$1($cg$16)($cg$19);
    $cg$3 = $_2_arg.$2($cg$4)($cg$13);
    let $cg$22 = null;
    let $cg$23 = null;
    let $cg$24 = null;
    const $cg$26 = $_2_arg.$1;
    $cg$24 = $cg$26.$2($_3_arg.$2)($_4_arg.$1);
    let $cg$27 = null;
    const $cg$29 = $_2_arg.$1;
    $cg$27 = $cg$29.$2($_3_arg.$1)($_4_arg.$2);
    $cg$23 = $_1_arg.$2($cg$24)($cg$27);
    let $cg$30 = null;
    const $cg$32 = $_2_arg.$1;
    let $cg$33 = null;
    const $cg$35 = $_2_arg.$1;
    $cg$33 = $cg$35.$2($_4_arg.$1)($_4_arg.$1);
    let $cg$36 = null;
    const $cg$38 = $_2_arg.$1;
    $cg$36 = $cg$38.$2($_4_arg.$2)($_4_arg.$2);
    $cg$30 = $cg$32.$1($cg$33)($cg$36);
    $cg$22 = $_2_arg.$2($cg$23)($cg$30);
    return new $HC_2_0$Data__Complex___58__43_($cg$3, $cg$22);
}

// Prelude.Functor.Prelude.List.List implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_($_2_arg($_3_arg.$1), Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_2_arg, $_3_arg.$2));
    } else {
        return $_3_arg;
    }
}

// Prelude.Functor.ParserCombinator.Parser implementation of Prelude.Functor.Functor, method map

function Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_inp){
    const $cg$2 = $_3_arg($_4_inp);
    if(($cg$2.type === 0)) {
        const $cg$4 = $cg$2.$1;
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair($cg$4.$1, $cg$4.$2));
    } else {
        return new $HC_1_1$ParserCombinator__ParseSuccess(Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0_58_map_39__58_0(null, null, null, null, $_2_arg, $cg$2.$1));
    }
}

// Data.IORef.Data.IORef.FFI_JS implementation of Data.IORef.HasReference, method newIORef'

function Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_newIORef_39__58_0($_0_arg, $_1_arg, $_2_in){
    const $_3_in = ({val: ($_1_arg)});
    return $_3_in;
}

// Data.IORef.Data.IORef.FFI_JS implementation of Data.IORef.HasReference, method readIORef'

function Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_readIORef_39__58_0($_0_arg, $_1_arg, $_2_in){
    const $_3_in = (($_1_arg).val);
    return $_3_in;
}

// Data.IORef.Data.IORef.FFI_JS implementation of Data.IORef.HasReference, method writeIORef'

function Data__IORef__Data__IORef___64_Data__IORef__HasReference_36_FFI_95_JS_58__33_writeIORef_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_w){
    return (($_1_arg).val = ($_2_arg));
}

// Prelude.Monad.Control.IOExcept.IOExcept' f e implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    return $partial_5_6$io_95_bind(null, null, null, $_4_arg, $partial_1_2$Prelude__Monad___123_Control__IOExcept___64_Prelude__Monad__Monad_36_IOExcept_39__32_f_32_e_58__33__62__62__61__58_0_95_lam_95_707_125_($_5_arg));
}

// Prelude.Monad.ParserCombinator.Parser implementation of Prelude.Monad.Monad, method >>=

function Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_inp){
    const $cg$2 = $_2_arg($_4_inp);
    if(($cg$2.type === 0)) {
        const $cg$9 = $cg$2.$1;
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair($cg$9.$1, $_4_inp));
    } else if(($cg$2.type === 1)) {
        const $cg$4 = $cg$2.$1;
        if(($cg$4.type === 1)) {
            const $cg$6 = $cg$4.$1;
            
            if(($cg$4.$2.type === 0)) {
                return $_3_arg($cg$6.$1)($cg$6.$2);
            } else {
                return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_4_inp));
            }
        } else {
            return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_4_inp));
        }
    } else {
        return new $HC_1_0$ParserCombinator__ParseError(new $HC_2_0$Builtins__MkPair("Error", $_4_inp));
    }
}

// Prelude.Interfaces.Data.Complex.Complex a implementation of Prelude.Interfaces.Num, method *

function Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Num_36_Complex_32_a_58__33__42__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    
    let $cg$3 = null;
    let $cg$4 = null;
    const $cg$6 = $_1_arg.$1;
    $cg$4 = $cg$6.$2($_2_arg.$1)($_3_arg.$1);
    let $cg$7 = null;
    const $cg$9 = $_1_arg.$1;
    $cg$7 = $cg$9.$2($_2_arg.$2)($_3_arg.$2);
    $cg$3 = $_1_arg.$2($cg$4)($cg$7);
    let $cg$10 = null;
    const $cg$12 = $_1_arg.$1;
    let $cg$13 = null;
    const $cg$15 = $_1_arg.$1;
    $cg$13 = $cg$15.$2($_2_arg.$2)($_3_arg.$1);
    let $cg$16 = null;
    const $cg$18 = $_1_arg.$1;
    $cg$16 = $cg$18.$2($_2_arg.$1)($_3_arg.$2);
    $cg$10 = $cg$12.$1($cg$13)($cg$16);
    return new $HC_2_0$Data__Complex___58__43_($cg$3, $cg$10);
}

// Prelude.Interfaces.Prelude.Interfaces.Char implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Char_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Double implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Int implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg === $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Interfaces.Integer implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if(((($_0_arg.equals($_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if(((((($_0_arg).compareTo(($_1_arg)) < 0)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Interfaces.Prelude.Nat.Nat implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Ord_36_Nat_58__33_compare_58_0($_0_arg, $_1_arg){
    for(;;) {
        
        if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return 0;
            } else {
                const $_2_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                return 1;
            }
        } else {
            const $_3_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
            
            if($_0_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return -1;
            } else {
                const $_4_in = $_0_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = $_4_in;
                $_1_arg = $_3_in;
            }
        }
    }
}

// Prelude.Interfaces.Ratio.Ratio a implementation of Prelude.Interfaces.Ord, method <=

function Prelude__Interfaces__Ratio___64_Prelude__Interfaces__Ord_36_Ratio_32_a_58__33__60__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    
    const $cg$4 = $_3_arg.$4;
    const $cg$6 = $_3_arg.$1;
    let $cg$5 = null;
    const $cg$8 = $cg$6.$1;
    $cg$5 = $cg$8.$2($_2_arg.$6)($_3_arg.$7);
    const $cg$10 = $_3_arg.$1;
    let $cg$9 = null;
    const $cg$12 = $cg$10.$1;
    $cg$9 = $cg$12.$2($_3_arg.$6)($_2_arg.$7);
    
    if(($cg$4.$2($cg$5)($cg$9) < 0)) {
        return true;
    } else {
        
        
        const $cg$17 = $_3_arg.$1;
        let $cg$16 = null;
        const $cg$19 = $cg$17.$1;
        $cg$16 = $cg$19.$2($_2_arg.$6)($_3_arg.$7);
        const $cg$21 = $_3_arg.$1;
        let $cg$20 = null;
        const $cg$23 = $cg$21.$1;
        $cg$20 = $cg$23.$2($_3_arg.$6)($_2_arg.$7);
        return $_3_arg.$2($cg$16)($cg$20);
    }
}

// Prelude.Interfaces.Ratio.Ratio a implementation of Prelude.Interfaces.Ord, method >=

function Prelude__Interfaces__Ratio___64_Prelude__Interfaces__Ord_36_Ratio_32_a_58__33__62__61__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    
    const $cg$4 = $_3_arg.$4;
    const $cg$6 = $_3_arg.$1;
    let $cg$5 = null;
    const $cg$8 = $cg$6.$1;
    $cg$5 = $cg$8.$2($_2_arg.$6)($_3_arg.$7);
    const $cg$10 = $_3_arg.$1;
    let $cg$9 = null;
    const $cg$12 = $cg$10.$1;
    $cg$9 = $cg$12.$2($_3_arg.$6)($_2_arg.$7);
    
    if(($cg$4.$2($cg$5)($cg$9) > 0)) {
        return true;
    } else {
        
        
        const $cg$17 = $_3_arg.$1;
        let $cg$16 = null;
        const $cg$19 = $cg$17.$1;
        $cg$16 = $cg$19.$2($_2_arg.$6)($_3_arg.$7);
        const $cg$21 = $_3_arg.$1;
        let $cg$20 = null;
        const $cg$23 = $cg$21.$1;
        $cg$20 = $cg$23.$2($_3_arg.$6)($_2_arg.$7);
        return $_3_arg.$2($cg$16)($cg$20);
    }
}

// Prelude.Interfaces.Prelude.Interfaces.String implementation of Prelude.Interfaces.Ord, method compare

function Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_String_58__33_compare_58_0($_0_arg, $_1_arg){
    
    if((((($_0_arg == $_1_arg)) ? 1|0 : 0|0) === 0)) {
        
        if((((($_0_arg < $_1_arg)) ? 1|0 : 0|0) === 0)) {
            return 1;
        } else {
            return -1;
        }
    } else {
        return 0;
    }
}

// Prelude.Show.Data.Complex.Complex a implementation of Prelude.Show.Show, method showPrec

function Prelude__Show__Data__Complex___64_Prelude__Show__Show_36_Complex_32_a_58__33_showPrec_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    let $cg$2 = null;
    if(($_2_arg.type === 4)) {
        $cg$2 = Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Ord_36_Nat_58__33_compare_58_0($_2_arg.$1, (new $JSRTS.jsbn.BigInteger(("6"))));
    } else {
        let $cg$3 = null;
        if(($_2_arg.type === 0)) {
            $cg$3 = (new $JSRTS.jsbn.BigInteger(("0")));
        } else {
            $cg$3 = (new $JSRTS.jsbn.BigInteger(("4")));
        }
        
        $cg$2 = Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($cg$3, (new $JSRTS.jsbn.BigInteger(("4"))));
    }
    
    let $cg$4 = null;
    if(($cg$2 > 0)) {
        $cg$4 = true;
    } else {
        
        if(($_2_arg.type === 4)) {
            $cg$4 = Prelude__Interfaces__Prelude__Nat___64_Prelude__Interfaces__Eq_36_Nat_58__33__61__61__58_0($_2_arg.$1, (new $JSRTS.jsbn.BigInteger(("6"))));
        } else {
            let $cg$6 = null;
            if(($_2_arg.type === 0)) {
                $cg$6 = (new $JSRTS.jsbn.BigInteger(("0")));
            } else {
                $cg$6 = (new $JSRTS.jsbn.BigInteger(("4")));
            }
            
            $cg$4 = $cg$6.equals((new $JSRTS.jsbn.BigInteger(("4"))));
        }
    }
    
    
    if($cg$4) {
        let $cg$10 = null;
        $cg$10 = $_1_arg.$2(new $HC_1_4$Prelude__Show__User((new $JSRTS.jsbn.BigInteger(("6")))))($_3_arg.$1);
        let $cg$11 = null;
        $cg$11 = $_1_arg.$2(new $HC_1_4$Prelude__Show__User((new $JSRTS.jsbn.BigInteger(("6")))))($_3_arg.$2);
        return ("(" + (($cg$10 + (" :+ " + $cg$11)) + ")"));
    } else {
        let $cg$8 = null;
        $cg$8 = $_1_arg.$2(new $HC_1_4$Prelude__Show__User((new $JSRTS.jsbn.BigInteger(("6")))))($_3_arg.$1);
        let $cg$9 = null;
        $cg$9 = $_1_arg.$2(new $HC_1_4$Prelude__Show__User((new $JSRTS.jsbn.BigInteger(("6")))))($_3_arg.$2);
        return ($cg$8 + (" :+ " + $cg$9));
    }
}

// Prelude.Traversable.Prelude.List implementation of Prelude.Traversable.Traversable, method traverse

function Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        
        let $cg$4 = null;
        let $cg$5 = null;
        $cg$5 = $_3_arg.$2(null)($partial_0_2$$_680_Util__replicateM_58_loop_58_0_95_lam());
        $cg$4 = $_3_arg.$3(null)(null)($cg$5)($_4_arg($_5_arg.$1));
        return $_3_arg.$3(null)(null)($cg$4)(Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, $_3_arg, $_4_arg, $_5_arg.$2));
    } else {
        
        return $_3_arg.$2(null)($HC_0_0$Prelude__List__Nil);
    }
}

// {Lists.accessors:caaaars:0_lam_593}

function $_593_Lists__accessors_58_caaaars_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_2_lift, $_3_lift);
}

// {Lists.accessors:caaaars:0_lam_594}

function $_594_Lists__accessors_58_caaaars_58_0_95_lam($_0_lift, $_1_lift){
    return new $HC_2_1$Prelude__List___58__58_($_1_lift, $HC_0_0$Prelude__List__Nil);
}

// {Lists.accessors:caaaars:0_lam_595}

function $_595_Lists__accessors_58_caaaars_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return Prelude__List___43__43_(null, Prelude__Functor__Prelude__List___64_Prelude__Functor__Functor_36_List_58__33_map_58_0(null, null, $_1_lift, $_0_lift), $_2_lift);
}

// {Lists.accessors:caaaars:0_lam_596}

function $_596_Lists__accessors_58_caaaars_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_1_3$$_595_Lists__accessors_58_caaaars_58_0_95_lam($_3_lift), $HC_0_0$Prelude__List__Nil, $_2_lift);
}

// {Lists.accessors:makeAccessor:0_lam_605}

function $_605_Lists__accessors_58_makeAccessor_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    
    if((((($_0_lift === "a")) ? 1|0 : 0|0) === 0)) {
        const $cg$3 = $_1_lift($_2_lift);
        if(($cg$3.type === 0)) {
            return new $HC_1_0$Prelude__Either__Left($cg$3.$1);
        } else {
            return Lists__cdr(new $HC_2_1$Prelude__List___58__58_($cg$3.$1, $HC_0_0$Prelude__List__Nil));
        }
    } else {
        const $cg$5 = $_1_lift($_2_lift);
        if(($cg$5.type === 0)) {
            return new $HC_1_0$Prelude__Either__Left($cg$5.$1);
        } else {
            return Lists__car(new $HC_2_1$Prelude__List___58__58_($cg$5.$1, $HC_0_0$Prelude__List__Nil));
        }
    }
}

// {Util.bindVars':bindHelper:0_lam_606}

function $_606_Util__bindVars_39__58_bindHelper_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $_11_in = $_3_lift($_4_lift);
    return $_2_lift($_11_in);
}

// {Util.bindVars':bindHelper:0_lam_608}

function $_608_Util__bindVars_39__58_bindHelper_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    const $_20_in = $_2_lift($_4_lift);
    const $_21_in = $_3_lift($_4_lift);
    return $_20_in($_21_in);
}

// {Util.defineVar':defineHelper:0_lam_615}

function $_615_Util__defineVar_39__58_defineHelper_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $_128_in = null;
    $_128_in = $_0_lift.$2(null)($_1_lift)($_4_lift);
    
    return $_0_lift.$3(null)($_1_lift)(Data__SortedMap__insert(null, null, $_2_lift, $_3_lift, $_128_in))($_4_lift);
}

// {Util.defineVar':defineHelper:0_lam_616}

function $_616_Util__defineVar_39__58_defineHelper_58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    let $_151_in = null;
    $_151_in = $_0_lift.$2(null)($_1_lift)($_4_lift);
    
    return $_0_lift.$3(null)($_1_lift)(Data__SortedMap__insert(null, null, $_2_lift, $_3_lift, $_151_in))($_4_lift);
}

// {Repl.evalExprList:traverse':0_lam_618}

function $_618_Repl__evalExprList_58_traverse_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Control__ST__Bind(Repl__evalExprList_58_traverse_39__58_0(null, null, null, null, null, null, $_0_lift, $_1_lift), $partial_1_2$Eval___123_evalArgs_95_257_125_($_2_lift));
}

// {Numbers.numMod:doMod:0_lam_619}

function $_619_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:174:25-34:unmatched case in Numbers.case block in case block in Numbers.numMod, doMod at Numbers.idr:173:25-34 at Numbers.idr:174:25-34 ***");
}

// {Numbers.numMod:doMod:0_lam_620}

function $_620_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:173:25-34:unmatched case in Numbers.case block in Numbers.numMod, doMod at Numbers.idr:173:25-34 ***");
}

// {Numbers.numMod:doMod:0_lam_621}

function $_621_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:170:25-34:unmatched case in Numbers.case block in case block in Numbers.numMod, doMod at Numbers.idr:169:25-34 at Numbers.idr:170:25-34 ***");
}

// {Numbers.numMod:doMod:0_lam_622}

function $_622_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:169:25-34:unmatched case in Numbers.case block in Numbers.numMod, doMod at Numbers.idr:169:25-34 ***");
}

// {Numbers.numMod:doMod:0_lam_640}

function $_640_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:166:25-34:unmatched case in Numbers.case block in case block in Numbers.numMod, doMod at Numbers.idr:165:25-34 at Numbers.idr:166:25-34 ***");
}

// {Numbers.numMod:doMod:0_lam_641}

function $_641_Numbers__numMod_58_doMod_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:165:25-34:unmatched case in Numbers.case block in Numbers.numMod, doMod at Numbers.idr:165:25-34 ***");
}

// {Numbers.numRem:doRem:0_lam_642}

function $_642_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:199:31-40:unmatched case in Numbers.case block in case block in Numbers.numRem, doRem at Numbers.idr:198:31-40 at Numbers.idr:199:31-40 ***");
}

// {Numbers.numRem:doRem:0_lam_643}

function $_643_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:198:31-40:unmatched case in Numbers.case block in Numbers.numRem, doRem at Numbers.idr:198:31-40 ***");
}

// {Numbers.numRem:doRem:0_lam_644}

function $_644_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:194:31-40:unmatched case in Numbers.case block in case block in Numbers.numRem, doRem at Numbers.idr:193:31-40 at Numbers.idr:194:31-40 ***");
}

// {Numbers.numRem:doRem:0_lam_645}

function $_645_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:193:31-40:unmatched case in Numbers.case block in Numbers.numRem, doRem at Numbers.idr:193:31-40 ***");
}

// {Numbers.numRem:doRem:0_lam_663}

function $_663_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:189:25-34:unmatched case in Numbers.case block in case block in Numbers.numRem, doRem at Numbers.idr:188:25-34 at Numbers.idr:189:25-34 ***");
}

// {Numbers.numRem:doRem:0_lam_664}

function $_664_Numbers__numRem_58_doRem_58_0_95_lam(){
    throw new Error(  "*** Numbers.idr:188:25-34:unmatched case in Numbers.case block in Numbers.numRem, doRem at Numbers.idr:188:25-34 ***");
}

// {ParseNumber.parseFloatHelper:helper:0_lam_667}

function $_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam($_0_lift, $_1_lift){
    return ($_0_lift + $_1_lift);
}

// {ParseNumber.parseFloatHelper:helper:0_lam_668}

function $_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam($_0_lift, $_1_lift){
    return ($_0_lift * $_1_lift);
}

// {ParseNumber.parseFloatHelper:helper:0_lam_669}

function $_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam($_0_lift){
    return (($_0_lift).intValue());
}

// {ParseNumber.parseFloatHelper:parseFloat':0_lam_671}

function $_671_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair(new $HC_1_5$DataTypes__LispFloat($_0_lift(ParseNumber__parseFloatHelper_58_helper_58_0(null, null, $_1_lift, $_2_lift($_3_lift), $_2_lift($_4_lift)))), $_5_lift), $HC_0_0$Prelude__List__Nil));
}

// {ParseNumber.parseFloatHelper:parseFloat':0_lam_672}

function $_672_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many1(null, $_0_lift), $partial_4_6$$_671_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_1_lift, $_2_lift, $_3_lift, $_4_lift));
}

// {ParseNumber.parseFloatHelper:parseFloat':0_lam_673}

function $_673_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$Parse___123_parseDottedList_95_378_125_()), $partial_5_6$$_672_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift));
}

// {ParseNumber.parseIntegerHelper:parseIntegerHelper':0_lam_674}

function $_674_ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return new $HC_1_4$DataTypes__LispInteger($_0_lift($_1_lift($_2_lift)));
}

// {Parse.parseString:escapedChar:0_lam_676}

function $_676_Parse__parseString_58_escapedChar_58_0_95_lam($_0_lift){
    return ($_0_lift === "\\");
}

// {Parse.parseString:escapedChar:0_lam_677}

function $_677_Parse__parseString_58_escapedChar_58_0_95_lam(){
    throw new Error(  "*** Parse.idr:42:28:unmatched case in Parse.case block in Parse.parseString, escapedChar at Parse.idr:42:28 ***");
}

// {Parse.parseString:escapedChar:0_lam_678}

function $_678_Parse__parseString_58_escapedChar_58_0_95_lam($_0_lift, $_1_lift){
    let $cg$1 = null;
    if(($_0_lift === "\"")) {
        $cg$1 = $_0_lift;
    } else if(($_0_lift === "\\")) {
        $cg$1 = $_0_lift;
    } else if(($_0_lift === "n")) {
        $cg$1 = "\n";
    } else if(($_0_lift === "r")) {
        $cg$1 = "\r";
    } else if(($_0_lift === "t")) {
        $cg$1 = "\t";
    } else {
        $cg$1 = new $JSRTS.Lazy((function(){
            return (function(){
                return $_677_Parse__parseString_58_escapedChar_58_0_95_lam();
            })();
        }));
    }
    
    return new $HC_1_1$ParserCombinator__ParseSuccess(new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($cg$1, $_1_lift), $HC_0_0$Prelude__List__Nil));
}

// {Parse.parseString:escapedChar:0_lam_679}

function $_679_Parse__parseString_58_escapedChar_58_0_95_lam($_0_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__oneOf("\\\"nrt"), $partial_0_2$$_678_Parse__parseString_58_escapedChar_58_0_95_lam());
}

// {Util.replicateM:loop:0_lam_680}

function $_680_Util__replicateM_58_loop_58_0_95_lam($_0_lift, $_1_lift){
    return new $HC_2_1$Prelude__List___58__58_($_0_lift, $_1_lift);
}

// {ParserCombinator.sepBy:separated:0_lam_683}

function $_683_ParserCombinator__sepBy_58_separated_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many_39_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_0_lift, $partial_1_2$Main___123_replEval_95_545_125_($_1_lift))), $partial_1_3$ParserCombinator___123_many1_95_278_125_($_2_lift));
}

// {Util.setVar':setHelper:0_lam_684}

function $_684_Util__setVar_39__58_setHelper_58_0_95_lam($_0_lift, $_1_lift){
    return true;
}

// {ParserCombinator.skipUntil:scan:0_lam_688}

function $_688_ParserCombinator__skipUntil_58_scan_58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__skipUntil_58_scan_58_0(null, null, $_0_lift, $_1_lift), $partial_0_2$ParserCombinator___123_skipMany_95_567_125_());
}

// {Data.SortedMap.treeToList:treeToList':0_lam_689}

function $_689_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift){
    return new $HC_2_1$Prelude__List___58__58_($_2_lift, Data__SortedMap__treeToList_58_treeToList_39__58_0(null, null, null, null, null, $_0_lift, $_1_lift));
}

// {Data.SortedMap.treeToList:treeToList':0_lam_691}

function $_691_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_1$Prelude__List___58__58_($_3_lift, Data__SortedMap__treeToList_58_treeToList_39__58_0(null, null, null, null, null, $partial_2_3$$_689_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam($_0_lift, $_1_lift), $_2_lift));
}

// {Eval.apply':evalBody:1_lam_710}

function $_710_Eval__apply_39__58_evalBody_58_1_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return new $HC_2_1$Control__ST__Bind(Eval__apply_39__58_evalBody_58_1(null, null, null, null, null, null, null, null, $_0_lift, $_1_lift, $_2_lift), $partial_1_2$Eval___123_evalArgs_95_257_125_($_3_lift));
}

// {Numbers.numDiv:doDiv:1_lam_718}

function $_718_Numbers__numDiv_58_doDiv_58_1_95_lam($_0_lift, $_1_lift){
    return ($_0_lift - $_1_lift);
}

// {Numbers.numDiv:doDiv:1_lam_722}

function $_722_Numbers__numDiv_58_doDiv_58_1_95_lam($_0_lift, $_1_lift){
    return ($_0_lift / $_1_lift);
}

// {Eval.eval:evalCond:11_lam_745}

function $_745_Eval__eval_58_evalCond_58_11_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 10)) {
        
        if((!$_4_lift.$1)) {
            return Eval__eval_58_evalCond_58_11(null, $_0_lift, null, $_1_lift, $_2_lift);
        } else {
            
            if(($_3_lift.type === 0)) {
                return new $HC_1_0$Control__ST__Pure($_4_lift);
            } else {
                return Eval__evalList(null, $_1_lift, $_0_lift, $_3_lift);
            }
        }
    } else {
        
        if(($_3_lift.type === 0)) {
            return new $HC_1_0$Control__ST__Pure($_4_lift);
        } else {
            return Eval__evalList(null, $_1_lift, $_0_lift, $_3_lift);
        }
    }
}

// {Eval.eval:evalCond:11_lam_746}

function $_746_Eval__eval_58_evalCond_58_11_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    
    if(($_4_lift.type === 10)) {
        
        if((!$_4_lift.$1)) {
            return Eval__eval_58_evalCond_58_11(null, $_0_lift, null, $_1_lift, $_2_lift);
        } else {
            
            if(($_3_lift.type === 0)) {
                return new $HC_1_0$Control__ST__Pure($_4_lift);
            } else {
                return Eval__evalList(null, $_1_lift, $_0_lift, $_3_lift);
            }
        }
    } else {
        
        if(($_3_lift.type === 0)) {
            return new $HC_1_0$Control__ST__Pure($_4_lift);
        } else {
            return Eval__evalList(null, $_1_lift, $_0_lift, $_3_lift);
        }
    }
}

// {Eval.eval:evalClauses:12_lam_750}

function $_750_Eval__eval_58_evalClauses_58_12_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    
    if($_5_lift) {
        return Eval__evalList(null, $_1_lift, $_0_lift, $_4_lift);
    } else {
        return Eval__eval_58_evalClauses_58_12(null, $_0_lift, null, null, $_1_lift, $_2_lift, $_3_lift);
    }
}

// {Eval.eval:inList:12_lam_751}

function $_751_Eval__eval_58_inList_58_12_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_3_lift.type === 10)) {
        
        if($_3_lift.$1) {
            return new $HC_1_0$Control__ST__Pure(true);
        } else {
            return Eval__eval_58_inList_58_12(null, null, null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($_1_lift, new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList($_2_lift), $HC_0_0$Prelude__List__Nil)));
        }
    } else {
        return Eval__eval_58_inList_58_12(null, null, null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($_1_lift, new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList($_2_lift), $HC_0_0$Prelude__List__Nil)));
    }
}

// {Eval.eval:inList:12_lam_752}

function $_752_Eval__eval_58_inList_58_12_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    
    if(($_3_lift.type === 10)) {
        
        if($_3_lift.$1) {
            return new $HC_1_0$Control__ST__Pure(true);
        } else {
            return Eval__eval_58_inList_58_12(null, null, null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($_1_lift, new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList($_2_lift), $HC_0_0$Prelude__List__Nil)));
        }
    } else {
        return Eval__eval_58_inList_58_12(null, null, null, null, $_0_lift, new $HC_2_1$Prelude__List___58__58_($_1_lift, new $HC_2_1$Prelude__List___58__58_(new $HC_1_2$DataTypes__LispList($_2_lift), $HC_0_0$Prelude__List__Nil)));
    }
}

// {Eval.eval:buildEnv:23_lam_755}

function $_755_Eval__eval_58_buildEnv_58_23_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift){
    return Eval__eval_58_buildEnv_58_23(null, null, null, null, $_0_lift, $_1_lift, $_2_lift, $_3_lift);
}

// {Eval.eval:buildEnv:23_lam_756}

function $_756_Eval__eval_58_buildEnv_58_23_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift, $_4_lift, $_5_lift){
    let $cg$1 = null;
    const $cg$3 = $_0_lift.$3;
    let $cg$4 = null;
    if(($_2_lift.type === 1)) {
        $cg$4 = $_2_lift.$1;
    } else {
        $cg$4 = new $JSRTS.Lazy((function(){
            return (function(){
                return Eval___123_eval_95_123_125_();
            })();
        }));
    }
    
    $cg$1 = $cg$3.$5($_1_lift)($cg$4)($_5_lift);
    return new $HC_2_1$Control__ST__Bind($cg$1, $partial_4_5$$_755_Eval__eval_58_buildEnv_58_23_95_lam($_0_lift, $_1_lift, $_3_lift, $_4_lift));
}

// {Eval.eval:buildEnv:24_lam_758}

function $_758_Eval__eval_58_buildEnv_58_24_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Eval__eval_58_buildEnv_58_24(null, null, null, null, $_0_lift, $_1_lift, $_2_lift);
}

// {Eval.eval:setRec:24_lam_759}

function $_759_Eval__eval_58_setRec_58_24_95_lam($_0_lift, $_1_lift, $_2_lift, $_3_lift){
    return Eval__eval_58_setRec_58_24(null, null, null, null, $_0_lift, $_1_lift, $_2_lift);
}

// Lists.accessors, caaaars

function Lists__accessors_58_caaaars_58_0(){
    return Prelude__List___43__43_(null, Util__replicateM_58_loop_58_0(null, null, null, new $HC_2_1$Prelude__List___58__58_("a", new $HC_2_1$Prelude__List___58__58_("d", $HC_0_0$Prelude__List__Nil)), new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$$_593_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_2$$_594_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_4$$_596_Lists__accessors_58_caaaars_58_0_95_lam()), 2), Prelude__List___43__43_(null, Util__replicateM_58_loop_58_0(null, null, null, new $HC_2_1$Prelude__List___58__58_("a", new $HC_2_1$Prelude__List___58__58_("d", $HC_0_0$Prelude__List__Nil)), new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$$_593_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_2$$_594_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_4$$_596_Lists__accessors_58_caaaars_58_0_95_lam()), 3), Util__replicateM_58_loop_58_0(null, null, null, new $HC_2_1$Prelude__List___58__58_("a", new $HC_2_1$Prelude__List___58__58_("d", $HC_0_0$Prelude__List__Nil)), new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_4$$_593_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_2$$_594_Lists__accessors_58_caaaars_58_0_95_lam(), $partial_0_4$$_596_Lists__accessors_58_caaaars_58_0_95_lam()), 4)));
}

// Lists.accessors, identity

function Lists__accessors_58_identity_58_0($_0_arg){
    
    if(($_0_arg.type === 1)) {
        
        if(($_0_arg.$2.type === 0)) {
            return new $HC_1_1$Prelude__Either__Right($_0_arg.$1);
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($_0_arg));
        }
    } else {
        return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($_0_arg));
    }
}

// Lists.accessors, makeAccessor

function Lists__accessors_58_makeAccessor_58_0($_0_arg){
    return Prelude__Foldable__Prelude__List___64_Prelude__Foldable__Foldable_36_List_58__33_foldr_58_0(null, null, $partial_0_3$$_605_Lists__accessors_58_makeAccessor_58_0_95_lam(), $partial_0_1$Lists__accessors_58_identity_58_0(), $_0_arg);
}

// Util.bindVars', bindHelper

function Util__bindVars_39__58_bindHelper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_in){
    const $_22_in = Prelude__Traversable__Prelude___64_Prelude__Traversable__Traversable_36_List_58__33_traverse_58_0(null, null, null, new $HC_3_0$Prelude__Applicative__Applicative_95_ictor($partial_0_5$$_606_Util__bindVars_39__58_bindHelper_58_0_95_lam(), $partial_0_3$Util___123_initEnv_39__95_271_125_(), $partial_0_5$$_608_Util__bindVars_39__58_bindHelper_58_0_95_lam()), $partial_3_5$Environment__addBinding(null, null, $_4_arg), $_3_arg)($_5_in);
    let $_32_in = null;
    $_32_in = $_4_arg.$1(null)(Data__SortedMap__fromList(null, null, new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Util___123_initEnv_39__95_273_125_(), $partial_0_2$Util___123_initEnv_39__95_274_125_(), $partial_0_2$Util___123_initEnv_39__95_275_125_()), $_22_in))($_5_in);
    return new $HC_2_1$Environment__Frame($_32_in, $_2_arg);
}

// ParseNumber.converterHelper, convert

function ParseNumber__converterHelper_58_convert_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    let $tco$$_3_arg = $_3_arg;
    for(;;) {
        
        if(($_4_arg.type === 1)) {
            $tco$$_3_arg = $_3_arg.add(Prelude__pow(null, new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $_1_arg, Prelude__List__length(null, $_4_arg.$2)).multiply($_0_arg($_4_arg.$1)));
            $_0_arg = $_0_arg;
            $_1_arg = $_1_arg;
            $_2_arg = null;
            $_3_arg = $tco$$_3_arg;
            $_4_arg = $_4_arg.$2;
        } else {
            return $_3_arg;
        }
    }
}

// Util.defineVar', defineHelper

function Util__defineVar_39__58_defineHelper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_9_in){
    
    if(($_6_arg.type === 1)) {
        let $_112_in = null;
        $_112_in = $_5_arg.$2(null)($_6_arg.$1)($_9_in);
        let $cg$8 = null;
        if(($_112_in.type === 0)) {
            $cg$8 = $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            $cg$8 = Data__SortedMap__treeLookup(null, null, $_112_in.$1, null, $_3_arg, $_112_in.$2);
        }
        
        
        if(($cg$8.type === 1)) {
            
            return $_5_arg.$3(null)($cg$8.$1)($_4_arg)($_9_in);
        } else {
            let $cg$10 = null;
            $cg$10 = $_5_arg.$1(null)($_4_arg);
            return io_95_bind(null, null, null, $cg$10, $partial_3_5$$_615_Util__defineVar_39__58_defineHelper_58_0_95_lam($_5_arg, $_6_arg.$1, $_3_arg), $_9_in);
        }
    } else {
        let $_135_in = null;
        $_135_in = $_5_arg.$2(null)($_6_arg.$1)($_9_in);
        let $cg$3 = null;
        if(($_135_in.type === 0)) {
            $cg$3 = $HC_0_0$Prelude__Maybe__Nothing;
        } else {
            $cg$3 = Data__SortedMap__treeLookup(null, null, $_135_in.$1, null, $_3_arg, $_135_in.$2);
        }
        
        
        if(($cg$3.type === 1)) {
            
            return $_5_arg.$3(null)($cg$3.$1)($_4_arg)($_9_in);
        } else {
            let $cg$5 = null;
            $cg$5 = $_5_arg.$1(null)($_4_arg);
            return io_95_bind(null, null, null, $cg$5, $partial_3_5$$_616_Util__defineVar_39__58_defineHelper_58_0_95_lam($_5_arg, $_6_arg.$1, $_3_arg), $_9_in);
        }
    }
}

// Repl.evalExprList, traverse'

function Repl__evalExprList_58_traverse_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_7_arg.type === 1)) {
        return new $HC_2_1$Control__ST__Bind($_6_arg($_7_arg.$1), $partial_2_3$$_618_Repl__evalExprList_58_traverse_39__58_0_95_lam($_6_arg, $_7_arg.$2));
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_0$Prelude__List__Nil);
    }
}

// Ratio.gcd, gcd'

function Ratio__gcd_58_gcd_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    for(;;) {
        let $cg$1 = null;
        const $cg$3 = $_3_arg.$1;
        $cg$1 = $cg$3.$3((new $JSRTS.jsbn.BigInteger(("0"))));
        
        if($_5_arg($_7_arg)($cg$1)) {
            return $_6_arg;
        } else {
            let $cg$5 = null;
            $cg$5 = $_3_arg.$3($_6_arg)($_7_arg);
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = $_3_arg;
            $_4_arg = null;
            $_5_arg = $_5_arg;
            $_6_arg = $_7_arg;
            $_7_arg = $cg$5;
        }
    }
}

// Util.getVar', getHelper

function Util__getVar_39__58_getHelper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_8_in){
    for(;;) {
        
        if(($_5_arg.type === 1)) {
            let $_41_in = null;
            $_41_in = $_4_arg.$2(null)($_5_arg.$1)($_8_in);
            let $cg$7 = null;
            if(($_41_in.type === 0)) {
                $cg$7 = $HC_0_0$Prelude__Maybe__Nothing;
            } else {
                $cg$7 = Data__SortedMap__treeLookup(null, null, $_41_in.$1, null, $_3_arg, $_41_in.$2);
            }
            
            
            if(($cg$7.type === 1)) {
                let $_49_in = null;
                $_49_in = $_4_arg.$2(null)($cg$7.$1)($_8_in);
                return new $HC_1_1$Prelude__Maybe__Just($_49_in);
            } else {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = null;
                $_3_arg = $_3_arg;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg.$2;
                $_8_in = $_8_in;
            }
        } else {
            let $_53_in = null;
            $_53_in = $_4_arg.$2(null)($_5_arg.$1)($_8_in);
            let $cg$3 = null;
            if(($_53_in.type === 0)) {
                $cg$3 = $HC_0_0$Prelude__Maybe__Nothing;
            } else {
                $cg$3 = Data__SortedMap__treeLookup(null, null, $_53_in.$1, null, $_3_arg, $_53_in.$2);
            }
            
            
            if(($cg$3.type === 1)) {
                let $_61_in = null;
                $_61_in = $_4_arg.$2(null)($cg$3.$1)($_8_in);
                return new $HC_1_1$Prelude__Maybe__Just($_61_in);
            } else {
                return $HC_0_0$Prelude__Maybe__Nothing;
            }
        }
    }
}

// Lists.listMember, helper

function Lists__listMember_58_helper_58_0($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            if(Prelude__Interfaces__DataTypes___64_Prelude__Interfaces__Eq_36_LispVal_58__33__61__61__58_0($_2_arg.$1, $_0_arg)) {
                return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, $_2_arg.$2)));
            } else {
                $_0_arg = $_0_arg;
                $_1_arg = null;
                $_2_arg = $_2_arg.$2;
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(false));
        }
    }
}

// Numbers.numAdd, doAdd

function Numbers__numAdd_58_doAdd_58_0($_0_arg){
    
    if(($_0_arg.type === 2)) {
        const $cg$3 = $_0_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$22 = $cg$3.$2;
                if(($cg$22.type === 1)) {
                    const $cg$24 = $cg$22.$1;
                    if(($cg$24.type === 6)) {
                        
                        if(($cg$22.$2.type === 0)) {
                            const $cg$27 = $cg$24.$1;
                            let $cg$26 = null;
                            const $cg$29 = $cg$5.$1;
                            $cg$26 = new $HC_2_0$Data__Complex___58__43_(($cg$29.$1 + $cg$27.$1), ($cg$29.$2 + $cg$27.$2));
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex($cg$26));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$17 = $cg$3.$2;
                if(($cg$17.type === 1)) {
                    const $cg$19 = $cg$17.$1;
                    if(($cg$19.type === 5)) {
                        
                        if(($cg$17.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat(($cg$5.$1 + $cg$19.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$12 = $cg$3.$2;
                if(($cg$12.type === 1)) {
                    const $cg$14 = $cg$12.$1;
                    if(($cg$14.type === 4)) {
                        
                        if(($cg$12.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger($cg$5.$1.add($cg$14.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            return Numbers__rationalBinaryOpHelper($partial_1_3$Ratio__rationalAdd(null), $cg$5.$1, $cg$9.$1, "+");
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in +"));
    }
}

// Numbers.numMod, doMod

function Numbers__numMod_58_doMod_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 2)) {
        const $cg$3 = $_2_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$38 = $cg$3.$2;
                if(($cg$38.type === 1)) {
                    const $cg$40 = $cg$38.$1;
                    if(($cg$40.type === 6)) {
                        
                        if(($cg$38.$2.type === 0)) {
                            const $_10_in = new $HC_1_6$DataTypes__LispComplex($cg$5.$1);
                            const $cg$43 = Numbers__numToInt($_10_in);
                            if(($cg$43.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$43.$1);
                            } else {
                                const $cg$45 = $cg$43.$1;
                                if(($cg$45.type === 4)) {
                                    const $cg$47 = Numbers__numToInt(new $HC_1_6$DataTypes__LispComplex($cg$40.$1));
                                    if(($cg$47.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_6$DataTypes__LispComplex($cg$40.$1));
                                    } else {
                                        const $cg$49 = $cg$47.$1;
                                        if(($cg$49.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_((($cg$45.$1.subtract((new $JSRTS.jsbn.BigInteger(Math.trunc((Math.floor(((($cg$45.$1).intValue()) / (($cg$49.$1).intValue())))))+ '')).multiply($cg$49.$1))).intValue()), 0.0)));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_619_Numbers__numMod_58_doMod_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_620_Numbers__numMod_58_doMod_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$25 = $cg$3.$2;
                if(($cg$25.type === 1)) {
                    const $cg$27 = $cg$25.$1;
                    if(($cg$27.type === 5)) {
                        
                        if(($cg$25.$2.type === 0)) {
                            const $_40_in = new $HC_1_5$DataTypes__LispFloat($cg$5.$1);
                            const $cg$30 = Numbers__numToInt($_40_in);
                            if(($cg$30.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$30.$1);
                            } else {
                                const $cg$32 = $cg$30.$1;
                                if(($cg$32.type === 4)) {
                                    const $cg$34 = Numbers__numToInt(new $HC_1_5$DataTypes__LispFloat($cg$27.$1));
                                    if(($cg$34.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_5$DataTypes__LispFloat($cg$27.$1));
                                    } else {
                                        const $cg$36 = $cg$34.$1;
                                        if(($cg$36.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat((($cg$32.$1.subtract((new $JSRTS.jsbn.BigInteger(Math.trunc((Math.floor(((($cg$32.$1).intValue()) / (($cg$36.$1).intValue())))))+ '')).multiply($cg$36.$1))).intValue())));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_621_Numbers__numMod_58_doMod_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_622_Numbers__numMod_58_doMod_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$20 = $cg$3.$2;
                if(($cg$20.type === 1)) {
                    const $cg$22 = $cg$20.$1;
                    if(($cg$22.type === 4)) {
                        
                        if(($cg$20.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger($cg$5.$1.subtract((new $JSRTS.jsbn.BigInteger(Math.trunc((Math.floor(((($cg$5.$1).intValue()) / (($cg$22.$1).intValue())))))+ '')).multiply($cg$22.$1))));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            const $_74_in = new $HC_1_7$DataTypes__LispRational($cg$5.$1);
                            const $cg$12 = Numbers__numToInt($_74_in);
                            if(($cg$12.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$12.$1);
                            } else {
                                const $cg$14 = $cg$12.$1;
                                if(($cg$14.type === 4)) {
                                    const $cg$16 = Numbers__numToInt(new $HC_1_7$DataTypes__LispRational($cg$9.$1));
                                    if(($cg$16.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_7$DataTypes__LispRational($cg$9.$1));
                                    } else {
                                        const $cg$18 = $cg$16.$1;
                                        if(($cg$18.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_7$DataTypes__LispRational(new $HC_7_0$Ratio_____37_(new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), $cg$14.$1.subtract((new $JSRTS.jsbn.BigInteger(Math.trunc((Math.floor(((($cg$14.$1).intValue()) / (($cg$18.$1).intValue())))))+ '')).multiply($cg$18.$1)), (new $JSRTS.jsbn.BigInteger(("1"))))));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_640_Numbers__numMod_58_doMod_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_641_Numbers__numMod_58_doMod_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in modulo"));
    }
}

// Numbers.numRem, doRem

function Numbers__numRem_58_doRem_58_0($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 2)) {
        const $cg$3 = $_2_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$38 = $cg$3.$2;
                if(($cg$38.type === 1)) {
                    const $cg$40 = $cg$38.$1;
                    if(($cg$40.type === 6)) {
                        
                        if(($cg$38.$2.type === 0)) {
                            const $_10_in = new $HC_1_6$DataTypes__LispComplex($cg$5.$1);
                            const $cg$43 = Numbers__numToInt($_10_in);
                            if(($cg$43.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$43.$1);
                            } else {
                                const $cg$45 = $cg$43.$1;
                                if(($cg$45.type === 4)) {
                                    const $cg$47 = Numbers__numToInt(new $HC_1_6$DataTypes__LispComplex($cg$40.$1));
                                    if(($cg$47.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_6$DataTypes__LispComplex($cg$40.$1));
                                    } else {
                                        const $cg$49 = $cg$47.$1;
                                        if(($cg$49.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex(new $HC_2_0$Data__Complex___58__43_(((Prelude__Interfaces__modBigInt($cg$45.$1, $cg$49.$1)).intValue()), 0.0)));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_642_Numbers__numRem_58_doRem_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_643_Numbers__numRem_58_doRem_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$25 = $cg$3.$2;
                if(($cg$25.type === 1)) {
                    const $cg$27 = $cg$25.$1;
                    if(($cg$27.type === 5)) {
                        
                        if(($cg$25.$2.type === 0)) {
                            const $_40_in = new $HC_1_5$DataTypes__LispFloat($cg$5.$1);
                            const $cg$30 = Numbers__numToInt($_40_in);
                            if(($cg$30.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$30.$1);
                            } else {
                                const $cg$32 = $cg$30.$1;
                                if(($cg$32.type === 4)) {
                                    const $cg$34 = Numbers__numToInt(new $HC_1_5$DataTypes__LispFloat($cg$27.$1));
                                    if(($cg$34.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_5$DataTypes__LispFloat($cg$27.$1));
                                    } else {
                                        const $cg$36 = $cg$34.$1;
                                        if(($cg$36.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat(((Prelude__Interfaces__modBigInt($cg$32.$1, $cg$36.$1)).intValue())));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_644_Numbers__numRem_58_doRem_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_645_Numbers__numRem_58_doRem_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$20 = $cg$3.$2;
                if(($cg$20.type === 1)) {
                    const $cg$22 = $cg$20.$1;
                    if(($cg$22.type === 4)) {
                        
                        if(($cg$20.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger(Prelude__Interfaces__modBigInt($cg$5.$1, $cg$22.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            const $_74_in = new $HC_1_7$DataTypes__LispRational($cg$5.$1);
                            const $cg$12 = Numbers__numToInt($_74_in);
                            if(($cg$12.type === 0)) {
                                return new $HC_1_0$Prelude__Either__Left($cg$12.$1);
                            } else {
                                const $cg$14 = $cg$12.$1;
                                if(($cg$14.type === 4)) {
                                    const $cg$16 = Numbers__numToInt(new $HC_1_7$DataTypes__LispRational($cg$9.$1));
                                    if(($cg$16.type === 0)) {
                                        return Numbers__numToInt(new $HC_1_7$DataTypes__LispRational($cg$9.$1));
                                    } else {
                                        const $cg$18 = $cg$16.$1;
                                        if(($cg$18.type === 4)) {
                                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_7$DataTypes__LispRational(new $HC_7_0$Ratio_____37_(new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), Prelude__Interfaces__modBigInt($cg$14.$1, $cg$18.$1), (new $JSRTS.jsbn.BigInteger(("1"))))));
                                        } else {
                                            return new $JSRTS.Lazy((function(){
                                                return (function(){
                                                    return $_663_Numbers__numRem_58_doRem_58_0_95_lam();
                                                })();
                                            }));
                                        }
                                    }
                                } else {
                                    return new $JSRTS.Lazy((function(){
                                        return (function(){
                                            return $_664_Numbers__numRem_58_doRem_58_0_95_lam();
                                        })();
                                    }));
                                }
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in remainder"));
    }
}

// Parse.parseBlockComment, takeAnything

function Parse__parseBlockComment_58_takeAnything_58_0(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $partial_0_1$ParserCombinator__item(), $partial_0_2$Parse___123_parseBlockComment_95_349_125_());
}

// ParseNumber.parseFloatHelper, helper

function ParseNumber__parseFloatHelper_58_helper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(((($_4_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) ? 1|0 : 0|0) === 0)) {
        const $_5_in = (($_4_arg).intValue());
        const $_6_in = (($_2_arg).intValue());
        return ((($_3_arg).intValue()) + ($_5_in / Prelude__pow(null, new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$$_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_2$$_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_1$$_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam()), $_6_in, (new $JSRTS.jsbn.BigInteger(Math.trunc((Math.floor((Math.log($_5_in) / Math.log($_6_in)))))+ '')).add((new $JSRTS.jsbn.BigInteger(("1")))))));
    } else {
        return (($_3_arg).intValue());
    }
}

// ParseNumber.parseFloatHelper, parseFloat'

function ParseNumber__parseFloatHelper_58_parseFloat_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__many1(null, $_1_arg), $partial_4_5$$_673_ParseNumber__parseFloatHelper_58_parseFloat_39__58_0_95_lam($_1_arg, $_3_arg, $_2_arg, $_0_arg));
}

// ParseNumber.parseIntegerHelper, parseIntegerHelper'

function ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0($_0_arg, $_1_arg, $_2_arg){
    return $partial_4_5$Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0(null, null, $partial_2_3$$_674_ParseNumber__parseIntegerHelper_58_parseIntegerHelper_39__58_0_95_lam($_2_arg, $_0_arg), ParserCombinator__many1(null, $_1_arg));
}

// Parse.parseString, escapedChar

function Parse__parseString_58_escapedChar_58_0(){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, ParserCombinator__sat($partial_0_1$$_676_Parse__parseString_58_escapedChar_58_0_95_lam()), $partial_0_1$$_679_Parse__parseString_58_escapedChar_58_0_95_lam());
}

// Util.replicateM, loop

function Util__replicateM_58_loop_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    let $cg$1 = null;
    if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Int_58__33_compare_58_0($_5_arg, 0) < 0)) {
        $cg$1 = true;
    } else {
        $cg$1 = ($_5_arg === 0);
    }
    
    
    if($cg$1) {
        
        return $_4_arg.$2(null)($HC_0_0$Prelude__List__Nil);
    } else {
        
        let $cg$4 = null;
        $cg$4 = $_4_arg.$1(null)(null)($partial_0_2$$_680_Util__replicateM_58_loop_58_0_95_lam())($_3_arg);
        return $_4_arg.$3(null)(null)($cg$4)(Util__replicateM_58_loop_58_0(null, null, null, $_3_arg, $_4_arg, ($_5_arg - 1)));
    }
}

// ParserCombinator.sepBy, separated

function ParserCombinator__sepBy_58_separated_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_2_arg, $partial_2_3$$_683_ParserCombinator__sepBy_58_separated_58_0_95_lam($_3_arg, $_2_arg));
}

// Util.setVar', setHelper

function Util__setVar_39__58_setHelper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_9_in){
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            let $_78_in = null;
            $_78_in = $_5_arg.$2(null)($_6_arg.$1)($_9_in);
            let $cg$7 = null;
            if(($_78_in.type === 0)) {
                $cg$7 = $HC_0_0$Prelude__Maybe__Nothing;
            } else {
                $cg$7 = Data__SortedMap__treeLookup(null, null, $_78_in.$1, null, $_3_arg, $_78_in.$2);
            }
            
            
            if(($cg$7.type === 1)) {
                let $cg$9 = null;
                $cg$9 = $_5_arg.$3(null)($cg$7.$1)($_4_arg);
                return io_95_bind(null, null, null, $cg$9, $partial_0_2$$_684_Util__setVar_39__58_setHelper_58_0_95_lam(), $_9_in);
            } else {
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = null;
                $_3_arg = $_3_arg;
                $_4_arg = $_4_arg;
                $_5_arg = $_5_arg;
                $_6_arg = $_6_arg.$2;
                $_9_in = $_9_in;
            }
        } else {
            let $_91_in = null;
            $_91_in = $_5_arg.$2(null)($_6_arg.$1)($_9_in);
            let $cg$3 = null;
            if(($_91_in.type === 0)) {
                $cg$3 = $HC_0_0$Prelude__Maybe__Nothing;
            } else {
                $cg$3 = Data__SortedMap__treeLookup(null, null, $_91_in.$1, null, $_3_arg, $_91_in.$2);
            }
            
            
            if(($cg$3.type === 1)) {
                let $cg$5 = null;
                $cg$5 = $_5_arg.$3(null)($cg$3.$1)($_4_arg);
                return io_95_bind(null, null, null, $cg$5, $partial_0_2$$_684_Util__setVar_39__58_setHelper_58_0_95_lam(), $_9_in);
            } else {
                return false;
            }
        }
    }
}

// Util.showEnv', printEnv

function Util__showEnv_39__58_printEnv_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_8_in){
    
    if(($_5_arg.type === 1)) {
        let $_22_in = null;
        $_22_in = $_4_arg.$2(null)($_5_arg.$1)($_8_in);
        const $_26_in = Util__showEnv_39__58_printBnd_58_0_58_bndHelp_58_0(null, null, null, $_3_arg, $_4_arg, null, Data__SortedMap__toList(null, null, $_22_in), $_8_in);
        const $_27_in = Util__showEnv_39__58_printEnv_58_0(null, null, null, $_3_arg, $_4_arg, $_5_arg.$2, $_8_in);
        return ("Frame<" + ($_26_in + ("," + ($_27_in + ">"))));
    } else {
        let $_28_in = null;
        $_28_in = $_4_arg.$2(null)($_5_arg.$1)($_8_in);
        const $_32_in = Util__showEnv_39__58_printBnd_58_0_58_bndHelp_58_0(null, null, null, $_3_arg, $_4_arg, null, Data__SortedMap__toList(null, null, $_28_in), $_8_in);
        return ("Global<" + ($_32_in + ">"));
    }
}

// ParserCombinator.skipUntil, scan

function ParserCombinator__skipUntil_58_scan_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    return $partial_3_4$ParserCombinator___60__124__62_(null, $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_2_arg, $partial_0_2$ParserCombinator___123_skipMany_95_567_125_()), $partial_4_5$Prelude__Monad__ParserCombinator___64_Prelude__Monad__Monad_36_Parser_58__33__62__62__61__58_0(null, null, $_3_arg, $partial_2_3$$_688_ParserCombinator__skipUntil_58_scan_58_0_95_lam($_2_arg, $_3_arg)));
}

// Data.SortedMap.treeToList, treeToList'

function Data__SortedMap__treeToList_58_treeToList_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    for(;;) {
        
        if(($_6_arg.type === 1)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = $partial_2_3$$_689_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam($_5_arg, $_6_arg.$3);
            $_6_arg = $_6_arg.$1;
        } else if(($_6_arg.type === 2)) {
            $_0_arg = null;
            $_1_arg = null;
            $_2_arg = null;
            $_3_arg = null;
            $_4_arg = null;
            $_5_arg = $partial_3_4$$_691_Data__SortedMap__treeToList_58_treeToList_39__58_0_95_lam($_5_arg, $_6_arg.$5, $_6_arg.$3);
            $_6_arg = $_6_arg.$1;
        } else {
            return $_5_arg(new $HC_2_0$Builtins__MkPair($_6_arg.$1, $_6_arg.$2));
        }
    }
}

// Numbers.variadicNumberOp, helper

function Numbers__variadicNumberOp_58_helper_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    for(;;) {
        
        if(($_3_arg.type === 1)) {
            const $cg$3 = Numbers__numCast(new $HC_2_1$Prelude__List___58__58_($_4_arg, new $HC_2_1$Prelude__List___58__58_($_3_arg.$1, $HC_0_0$Prelude__List__Nil)));
            if(($cg$3.type === 0)) {
                return new $HC_1_0$Prelude__Either__Left($cg$3.$1);
            } else {
                const $cg$5 = $_1_arg($cg$3.$1);
                if(($cg$5.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left($cg$5.$1);
                } else {
                    $_0_arg = null;
                    $_1_arg = $_1_arg;
                    $_2_arg = null;
                    $_3_arg = $_3_arg.$2;
                    $_4_arg = $cg$5.$1;
                }
            }
        } else {
            return new $HC_1_1$Prelude__Either__Right($_4_arg);
        }
    }
}

// Prelude.Functor.ParserCombinator.Parser implementation of Prelude.Functor.Functor, method map, map'

function Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0_58_map_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        const $cg$3 = $_5_arg.$1;
        return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_4_arg($cg$3.$1), $cg$3.$2), Prelude__Functor__ParserCombinator___64_Prelude__Functor__Functor_36_Parser_58__33_map_58_0_58_map_39__58_0(null, null, null, null, $_4_arg, $_5_arg.$2));
    } else {
        return $_5_arg;
    }
}

// Prelude.Show.Prelude.Show.List a implementation of Prelude.Show.Show, method show, show'

function Prelude__Show__Prelude__Show___64_Prelude__Show__Show_36_List_32_a_58__33_show_58_0_58_show_39__58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    for(;;) {
        
        if(($_4_arg.type === 1)) {
            
            if(($_4_arg.$2.type === 0)) {
                let $cg$4 = null;
                $cg$4 = $_2_arg.$1($_4_arg.$1);
                return ($_3_arg + $cg$4);
            } else {
                let $cg$3 = null;
                $cg$3 = $_2_arg.$1($_4_arg.$1);
                $_0_arg = null;
                $_1_arg = null;
                $_2_arg = $_2_arg;
                $_3_arg = ($_3_arg + ($cg$3 + ", "));
                $_4_arg = $_4_arg.$2;
            }
        } else {
            return $_3_arg;
        }
    }
}

// Util.showEnv', printBnd, bndHelp

function Util__showEnv_39__58_printBnd_58_0_58_bndHelp_58_0($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_11_in){
    
    if(($_6_arg.type === 1)) {
        const $cg$3 = $_6_arg.$1;
        let $_31_in = null;
        $_31_in = $_4_arg.$2(null)($cg$3.$2)($_11_in);
        const $_35_in = Util__showEnv_39__58_printBnd_58_0_58_bndHelp_58_0(null, null, null, $_3_arg, $_4_arg, null, $_6_arg.$2, $_11_in);
        let $cg$5 = null;
        $cg$5 = $_3_arg.$1($_31_in);
        return (($cg$3.$1 + (": " + $cg$5)) + ("," + $_35_in));
    } else {
        return "";
    }
}

// Eval.apply', evalBody

function Eval__apply_39__58_evalBody_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg, $_8_arg, $_9_arg, $_10_arg){
    
    if(($_10_arg.type === 1)) {
        return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_8_arg, $_9_arg, $_10_arg.$1), $partial_3_4$$_710_Eval__apply_39__58_evalBody_58_1_95_lam($_8_arg, $_9_arg, $_10_arg.$2));
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_0$Prelude__List__Nil);
    }
}

// Eval.apply', varargs'

function Eval__apply_39__58_varargs_39__58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_2_arg.type === 1)) {
        return new $HC_2_1$Prelude__List___58__58_(new $HC_2_0$Builtins__MkPair($_2_arg.$1, new $HC_1_2$DataTypes__LispList(Prelude__List__drop(null, Prelude__List__length(null, $_1_arg), $_5_arg))), $HC_0_0$Prelude__List__Nil);
    } else {
        return $HC_0_0$Prelude__List__Nil;
    }
}

// Lists.listAppend, helper

function Lists__listAppend_58_helper_58_1($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            const $cg$3 = $_2_arg.$1;
            if(($cg$3.type === 3)) {
                
                if(($_2_arg.$2.type === 0)) {
                    return new $HC_1_1$Prelude__Either__Right(new $HC_2_3$DataTypes__LispDottedList(Prelude__List___43__43_(null, $_1_arg, $cg$3.$1), new $JSRTS.Lazy((function(){
                        return (function(){
                            return Lists___123_cdr_95_12_125_($cg$3.$2);
                        })();
                    }))));
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_2_arg.$1));
                }
            } else {
                
                if(($_2_arg.$2.type === 0)) {
                    
                    if(($_1_arg.type === 0)) {
                        return new $HC_1_1$Prelude__Either__Right($_2_arg.$1);
                    } else {
                        return new $HC_1_1$Prelude__Either__Right(new $HC_2_3$DataTypes__LispDottedList($_1_arg, new $JSRTS.Lazy((function(){
                            return (function(){
                                return Lists___123_cons_95_14_125_($_2_arg.$1);
                            })();
                        }))));
                    }
                } else {
                    const $cg$6 = $_2_arg.$1;
                    if(($cg$6.type === 2)) {
                        $_0_arg = null;
                        $_1_arg = Prelude__List___43__43_(null, $_1_arg, $cg$6.$1);
                        $_2_arg = $_2_arg.$2;
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_2_1$DataTypes__TypeMismatch("list", $_2_arg.$1));
                    }
                }
            }
        } else if(($_2_arg.type === 0)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_2$DataTypes__LispList($_1_arg));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unknown error in append"));
        }
    }
}

// Numbers.numBoolBinopEq, fn

function Numbers__numBoolBinopEq_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0(null, $partial_0_2$Primitives___123_eqv_95_22_125_(), $_2_arg.$1, $_3_arg.$1)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in ="));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(($_2_arg.$1 === $_3_arg.$1)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in ="));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($_2_arg.$1.equals($_3_arg.$1)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in ="));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            const $cg$4 = $_3_arg.$1;
            let $cg$3 = null;
            const $cg$6 = $_2_arg.$1;
            const $cg$8 = $cg$4.$1;
            let $cg$7 = null;
            const $cg$10 = $cg$8.$1;
            $cg$7 = $cg$10.$2($cg$6.$6)($cg$4.$7);
            const $cg$12 = $cg$4.$1;
            let $cg$11 = null;
            const $cg$14 = $cg$12.$1;
            $cg$11 = $cg$14.$2($cg$4.$6)($cg$6.$7);
            $cg$3 = $cg$4.$2($cg$7)($cg$11);
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$3));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in ="));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in ="));
    }
}

// Numbers.numBoolBinopGt, fn

function Numbers__numBoolBinopGt_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("> not defined for complex numbers"));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >"));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool((!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) > 0)))));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >"));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool((!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) > 0)))));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >"));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            const $cg$4 = $_3_arg.$1;
            let $cg$3 = null;
            const $cg$6 = $_2_arg.$1;
            const $cg$8 = $cg$4.$4;
            const $cg$10 = $cg$4.$1;
            let $cg$9 = null;
            const $cg$12 = $cg$10.$1;
            $cg$9 = $cg$12.$2($cg$6.$6)($cg$4.$7);
            const $cg$14 = $cg$4.$1;
            let $cg$13 = null;
            const $cg$16 = $cg$14.$1;
            $cg$13 = $cg$16.$2($cg$4.$6)($cg$6.$7);
            $cg$3 = (!(!($cg$8.$2($cg$9)($cg$13) > 0)));
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$3));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >"));
    }
}

// Numbers.numBoolBinopGte, fn

function Numbers__numBoolBinopGte_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default(">= not defined for complex numbers"));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >="));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            let $cg$6 = null;
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) > 0)) {
                $cg$6 = true;
            } else {
                $cg$6 = ($_2_arg.$1 === $_3_arg.$1);
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$6));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >="));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            let $cg$4 = null;
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) > 0)) {
                $cg$4 = true;
            } else {
                $cg$4 = $_2_arg.$1.equals($_3_arg.$1);
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$4));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >="));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(Prelude__Interfaces__Ratio___64_Prelude__Interfaces__Ord_36_Ratio_32_a_58__33__62__61__58_0(null, null, $_2_arg.$1, $_3_arg.$1)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >="));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in >="));
    }
}

// Numbers.numBoolBinopLt, fn

function Numbers__numBoolBinopLt_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("< not defined for complex numbers"));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <"));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool((!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) < 0)))));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <"));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool((!(!(Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) < 0)))));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <"));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            const $cg$4 = $_3_arg.$1;
            let $cg$3 = null;
            const $cg$6 = $_2_arg.$1;
            const $cg$8 = $cg$4.$4;
            const $cg$10 = $cg$4.$1;
            let $cg$9 = null;
            const $cg$12 = $cg$10.$1;
            $cg$9 = $cg$12.$2($cg$6.$6)($cg$4.$7);
            const $cg$14 = $cg$4.$1;
            let $cg$13 = null;
            const $cg$16 = $cg$14.$1;
            $cg$13 = $cg$16.$2($cg$4.$6)($cg$6.$7);
            $cg$3 = (!(!($cg$8.$2($cg$9)($cg$13) < 0)));
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$3));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <"));
    }
}

// Numbers.numBoolBinopLte, fn

function Numbers__numBoolBinopLte_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("<= not defined for complex numbers"));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            let $cg$6 = null;
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Double_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) < 0)) {
                $cg$6 = true;
            } else {
                $cg$6 = ($_2_arg.$1 === $_3_arg.$1);
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$6));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            let $cg$4 = null;
            if((Prelude__Interfaces__Prelude__Interfaces___64_Prelude__Interfaces__Ord_36_Integer_58__33_compare_58_0($_2_arg.$1, $_3_arg.$1) < 0)) {
                $cg$4 = true;
            } else {
                $cg$4 = $_2_arg.$1.equals($_3_arg.$1);
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$4));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool(Prelude__Interfaces__Ratio___64_Prelude__Interfaces__Ord_36_Ratio_32_a_58__33__60__61__58_0(null, null, $_2_arg.$1, $_3_arg.$1)));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in <="));
    }
}

// Numbers.numBoolBinopNeq, fn

function Numbers__numBoolBinopNeq_58_fn_58_1($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    
    if(($_3_arg.type === 6)) {
        
        if(($_2_arg.type === 6)) {
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool((!(!(!Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0(null, $partial_0_2$Primitives___123_eqv_95_22_125_(), $_2_arg.$1, $_3_arg.$1))))));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /="));
        }
    } else if(($_3_arg.type === 5)) {
        
        if(($_2_arg.type === 5)) {
            let $cg$18 = null;
            if((((($_2_arg.$1 === $_3_arg.$1)) ? 1|0 : 0|0) === 0)) {
                $cg$18 = true;
            } else {
                $cg$18 = false;
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$18));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /="));
        }
    } else if(($_3_arg.type === 4)) {
        
        if(($_2_arg.type === 4)) {
            let $cg$16 = null;
            if(((($_2_arg.$1.equals($_3_arg.$1)) ? 1|0 : 0|0) === 0)) {
                $cg$16 = true;
            } else {
                $cg$16 = false;
            }
            
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$16));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /="));
        }
    } else if(($_3_arg.type === 7)) {
        
        if(($_2_arg.type === 7)) {
            const $cg$4 = $_3_arg.$1;
            let $cg$3 = null;
            const $cg$6 = $_2_arg.$1;
            const $cg$8 = $cg$4.$1;
            let $cg$7 = null;
            const $cg$10 = $cg$8.$1;
            $cg$7 = $cg$10.$2($cg$6.$6)($cg$4.$7);
            const $cg$12 = $cg$4.$1;
            let $cg$11 = null;
            const $cg$14 = $cg$12.$1;
            $cg$11 = $cg$14.$2($cg$4.$6)($cg$6.$7);
            $cg$3 = (!(!(!$cg$4.$2($cg$7)($cg$11))));
            return new $HC_1_1$Prelude__Either__Right(new $HC_1_10$DataTypes__LispBool($cg$3));
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /="));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /="));
    }
}

// Numbers.numDiv, doDiv

function Numbers__numDiv_58_doDiv_58_1($_0_arg, $_1_arg, $_2_arg){
    
    if(($_2_arg.type === 2)) {
        const $cg$3 = $_2_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$25 = $cg$3.$2;
                if(($cg$25.type === 1)) {
                    const $cg$27 = $cg$25.$1;
                    if(($cg$27.type === 6)) {
                        
                        if(($cg$25.$2.type === 0)) {
                            
                            if(Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Eq_36_Complex_32_a_58__33__61__61__58_0(null, $partial_0_2$Primitives___123_eqv_95_22_125_(), $cg$27.$1, new $HC_2_0$Data__Complex___58__43_(0.0, 0.0))) {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Zero division error"));
                            } else {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex(Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Fractional_36_Complex_32_a_58__33__47__58_0(null, new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$$_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_2$$_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_1$$_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam()), $partial_0_2$$_718_Numbers__numDiv_58_doDiv_58_1_95_lam()), new $HC_2_0$Prelude__Interfaces__Fractional_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$$_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_2$$_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_1$$_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam()), $partial_0_2$$_722_Numbers__numDiv_58_doDiv_58_1_95_lam()), $cg$5.$1, $cg$27.$1)));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$19 = $cg$3.$2;
                if(($cg$19.type === 1)) {
                    const $cg$21 = $cg$19.$1;
                    if(($cg$21.type === 5)) {
                        
                        if(($cg$19.$2.type === 0)) {
                            
                            if((((($cg$21.$1 === 0.0)) ? 1|0 : 0|0) === 0)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat(($cg$5.$1 / $cg$21.$1)));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Zero division error"));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$12 = $cg$3.$2;
                if(($cg$12.type === 1)) {
                    const $cg$14 = $cg$12.$1;
                    if(($cg$14.type === 4)) {
                        
                        if(($cg$12.$2.type === 0)) {
                            const $cg$17 = Ratio___58__37_(null, new $HC_3_0$Prelude__Interfaces__Integral_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_292_125_(), $partial_0_2$Numbers___123_numCast_95_293_125_()), $partial_0_2$Numbers___123_numCast_95_294_125_(), new $HC_2_0$Prelude__Interfaces__Abs_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_1$Numbers___123_numCast_95_298_125_()), new $HC_3_0$Prelude__Interfaces__Ord_95_ictor($partial_0_2$Numbers___123_numCast_95_294_125_(), $partial_0_2$Numbers___123_numCast_95_300_125_(), $partial_0_2$Numbers___123_numCast_95_301_125_()), new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$Numbers___123_numCast_95_289_125_(), $partial_0_2$Numbers___123_numCast_95_290_125_(), $partial_0_1$Lists___123_cons_95_14_125_()), $partial_0_2$Numbers___123_numCast_95_305_125_()), $cg$5.$1, $cg$14.$1);
                            if(($cg$17.type === 1)) {
                                return new $HC_1_1$Prelude__Either__Right(new $HC_1_7$DataTypes__LispRational($cg$17.$1));
                            } else {
                                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Zero division error"));
                            }
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            return Numbers__rationalBinaryOpHelper($partial_1_3$Ratio__rationalDiv(null), $cg$5.$1, $cg$9.$1, "/");
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in /"));
    }
}

// Numbers.numMul, doMul

function Numbers__numMul_58_doMul_58_1($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 2)) {
        const $cg$3 = $_1_arg.$1;
        if(($cg$3.type === 1)) {
            const $cg$5 = $cg$3.$1;
            if(($cg$5.type === 6)) {
                const $cg$22 = $cg$3.$2;
                if(($cg$22.type === 1)) {
                    const $cg$24 = $cg$22.$1;
                    if(($cg$24.type === 6)) {
                        
                        if(($cg$22.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_6$DataTypes__LispComplex(Prelude__Interfaces__Data__Complex___64_Prelude__Interfaces__Num_36_Complex_32_a_58__33__42__58_0(null, new $HC_2_0$Prelude__Interfaces__Neg_95_ictor(new $HC_3_0$Prelude__Interfaces__Num_95_ictor($partial_0_2$$_667_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_2$$_668_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam(), $partial_0_1$$_669_ParseNumber__parseFloatHelper_58_helper_58_0_95_lam()), $partial_0_2$$_718_Numbers__numDiv_58_doDiv_58_1_95_lam()), $cg$5.$1, $cg$24.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                }
            } else if(($cg$5.type === 5)) {
                const $cg$17 = $cg$3.$2;
                if(($cg$17.type === 1)) {
                    const $cg$19 = $cg$17.$1;
                    if(($cg$19.type === 5)) {
                        
                        if(($cg$17.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_5$DataTypes__LispFloat(($cg$5.$1 * $cg$19.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                }
            } else if(($cg$5.type === 4)) {
                const $cg$12 = $cg$3.$2;
                if(($cg$12.type === 1)) {
                    const $cg$14 = $cg$12.$1;
                    if(($cg$14.type === 4)) {
                        
                        if(($cg$12.$2.type === 0)) {
                            return new $HC_1_1$Prelude__Either__Right(new $HC_1_4$DataTypes__LispInteger($cg$5.$1.multiply($cg$14.$1)));
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                }
            } else if(($cg$5.type === 7)) {
                const $cg$7 = $cg$3.$2;
                if(($cg$7.type === 1)) {
                    const $cg$9 = $cg$7.$1;
                    if(($cg$9.type === 7)) {
                        
                        if(($cg$7.$2.type === 0)) {
                            return Numbers__rationalBinaryOpHelper($partial_1_3$Ratio__rationalMul(null), $cg$5.$1, $cg$9.$1, "*");
                        } else {
                            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                        }
                    } else {
                        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                    }
                } else {
                    return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
                }
            } else {
                return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
            }
        } else {
            return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
        }
    } else {
        return new $HC_1_0$Prelude__Either__Left(new $HC_1_6$DataTypes__Default("Unexpected error in *"));
    }
}

// Primitives.eqv, eqvPairs

function Primitives__eqv_58_eqvPairs_58_9($_0_arg, $_1_arg, $_2_arg, $_3_arg){
    for(;;) {
        
        if(($_3_arg.type === 0)) {
            
            if(($_2_arg.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(true);
            } else {
                return new $HC_1_1$Prelude__Either__Right(false);
            }
        } else {
            
            if(($_2_arg.type === 0)) {
                return new $HC_1_1$Prelude__Either__Right(false);
            } else {
                
                
                const $cg$6 = Primitives__eqv(new $HC_2_1$Prelude__List___58__58_($_2_arg.$1, new $HC_2_1$Prelude__List___58__58_($_3_arg.$1, $HC_0_0$Prelude__List__Nil)));
                if(($cg$6.type === 0)) {
                    return new $HC_1_0$Prelude__Either__Left($cg$6.$1);
                } else {
                    const $cg$8 = $cg$6.$1;
                    if(($cg$8.type === 10)) {
                        const $cg$10 = $cg$8.$1;
                        if((!$cg$10)) {
                            return new $HC_1_1$Prelude__Either__Right(false);
                        } else if($cg$10) {
                            $_0_arg = null;
                            $_1_arg = null;
                            $_2_arg = $_2_arg.$2;
                            $_3_arg = $_3_arg.$2;
                        } else {
                            return new $HC_1_1$Prelude__Either__Right(false);
                        }
                    } else {
                        return new $HC_1_1$Prelude__Either__Right(false);
                    }
                }
            }
        }
    }
}

// Prelude.Show.showLitChar, asciiTab

function Prelude__Show__showLitChar_58_asciiTab_58_10($_0_arg){
    return new $HC_2_1$Prelude__List___58__58_("NUL", new $HC_2_1$Prelude__List___58__58_("SOH", new $HC_2_1$Prelude__List___58__58_("STX", new $HC_2_1$Prelude__List___58__58_("ETX", new $HC_2_1$Prelude__List___58__58_("EOT", new $HC_2_1$Prelude__List___58__58_("ENQ", new $HC_2_1$Prelude__List___58__58_("ACK", new $HC_2_1$Prelude__List___58__58_("BEL", new $HC_2_1$Prelude__List___58__58_("BS", new $HC_2_1$Prelude__List___58__58_("HT", new $HC_2_1$Prelude__List___58__58_("LF", new $HC_2_1$Prelude__List___58__58_("VT", new $HC_2_1$Prelude__List___58__58_("FF", new $HC_2_1$Prelude__List___58__58_("CR", new $HC_2_1$Prelude__List___58__58_("SO", new $HC_2_1$Prelude__List___58__58_("SI", new $HC_2_1$Prelude__List___58__58_("DLE", new $HC_2_1$Prelude__List___58__58_("DC1", new $HC_2_1$Prelude__List___58__58_("DC2", new $HC_2_1$Prelude__List___58__58_("DC3", new $HC_2_1$Prelude__List___58__58_("DC4", new $HC_2_1$Prelude__List___58__58_("NAK", new $HC_2_1$Prelude__List___58__58_("SYN", new $HC_2_1$Prelude__List___58__58_("ETB", new $HC_2_1$Prelude__List___58__58_("CAN", new $HC_2_1$Prelude__List___58__58_("EM", new $HC_2_1$Prelude__List___58__58_("SUB", new $HC_2_1$Prelude__List___58__58_("ESC", new $HC_2_1$Prelude__List___58__58_("FS", new $HC_2_1$Prelude__List___58__58_("GS", new $HC_2_1$Prelude__List___58__58_("RS", new $HC_2_1$Prelude__List___58__58_("US", $HC_0_0$Prelude__List__Nil))))))))))))))))))))))))))))))));
}

// Prelude.Show.showLitChar, getAt

function Prelude__Show__showLitChar_58_getAt_58_10($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_2_arg.type === 1)) {
            
            if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return new $HC_1_1$Prelude__Maybe__Just($_2_arg.$1);
            } else {
                const $_5_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = null;
                $_1_arg = $_5_in;
                $_2_arg = $_2_arg.$2;
            }
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    }
}

// Eval.eval, evalCond

function Eval__eval_58_evalCond_58_11($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg){
    
    if(($_4_arg.type === 1)) {
        const $cg$4 = $_4_arg.$1;
        if(($cg$4.type === 2)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                const $cg$10 = $cg$7.$1;
                if(($cg$10.type === 1)) {
                    
                    if(($cg$10.$1 === "else")) {
                        
                        if(($_4_arg.$2.type === 0)) {
                            return Eval__evalList(null, $_3_arg, $_1_arg, $cg$7.$2);
                        } else {
                            
                            return $_3_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("cond: bad syntax (`else` clause must be last)"));
                        }
                    } else {
                        return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_3_arg, $_1_arg, $cg$7.$1), $partial_4_5$$_745_Eval__eval_58_evalCond_58_11_95_lam($_1_arg, $_3_arg, $_4_arg.$2, $cg$7.$2));
                    }
                } else {
                    return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_3_arg, $_1_arg, $cg$7.$1), $partial_4_5$$_746_Eval__eval_58_evalCond_58_11_95_lam($_1_arg, $_3_arg, $_4_arg.$2, $cg$7.$2));
                }
            } else {
                
                return $_3_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default(("[" + (Prelude__Show__Prelude__Show___64_Prelude__Show__Show_36_List_32_a_58__33_show_58_0_58_show_39__58_0(null, null, new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()), "", $_4_arg) + "]"))));
            }
        } else {
            
            return $_3_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default(("[" + (Prelude__Show__Prelude__Show___64_Prelude__Show__Show_36_List_32_a_58__33_show_58_0_58_show_39__58_0(null, null, new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()), "", $_4_arg) + "]"))));
        }
    } else if(($_4_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
    } else {
        
        return $_3_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default(("[" + (Prelude__Show__Prelude__Show___64_Prelude__Show__Show_36_List_32_a_58__33_show_58_0_58_show_39__58_0(null, null, new $HC_2_0$Prelude__Show__Show_95_ictor($partial_0_1$DataTypes__showVal(), $partial_0_1$Eval___123_eval_95_24_125_()), "", $_4_arg) + "]"))));
    }
}

// Eval.eval, evalClauses

function Eval__eval_58_evalClauses_58_12($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        const $cg$4 = $_6_arg.$1;
        if(($cg$4.type === 2)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                return new $HC_2_1$Control__ST__Bind(new $HC_2_10$Control__ST__Call(Eval__eval_58_inList_58_12(null, null, null, null, $_4_arg, new $HC_2_1$Prelude__List___58__58_($_5_arg, new $HC_2_1$Prelude__List___58__58_($cg$7.$1, $HC_0_0$Prelude__List__Nil))), $HC_0_0$Control__ST__SubNil), $partial_5_6$$_750_Eval__eval_58_evalClauses_58_12_95_lam($_1_arg, $_4_arg, $_5_arg, $_6_arg.$2, $cg$7.$2));
            } else if(($cg$7.type === 0)) {
                
                if(($_6_arg.$2.type === 0)) {
                    return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
                } else {
                    
                    return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                }
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
            }
        } else {
            
            return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
        }
    } else if(($_6_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure($HC_0_13$DataTypes__LispVoid);
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
    }
}

// Eval.eval, inList

function Eval__eval_58_inList_58_12($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        const $cg$4 = $_5_arg.$2;
        if(($cg$4.type === 1)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                
                if(($cg$7.$1 === "else")) {
                    
                    if(($cg$4.$2.type === 0)) {
                        return new $HC_1_0$Control__ST__Pure(true);
                    } else {
                        
                        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                    }
                } else {
                    
                    return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                }
            } else if(($cg$7.type === 2)) {
                const $cg$10 = $cg$7.$1;
                if(($cg$10.type === 1)) {
                    const $cg$15 = $cg$10.$1;
                    if(($cg$15.type === 1)) {
                        
                        if(($cg$15.$1 === "else")) {
                            
                            if(($cg$4.$2.type === 0)) {
                                
                                return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax (`else` clause must be last)"));
                            } else {
                                
                                return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                            }
                        } else {
                            
                            if(($cg$4.$2.type === 0)) {
                                const $cg$28 = Primitives__eqv(new $HC_2_1$Prelude__List___58__58_($cg$10.$1, new $HC_2_1$Prelude__List___58__58_($_5_arg.$1, $HC_0_0$Prelude__List__Nil)));
                                let $cg$27 = null;
                                if(($cg$28.type === 0)) {
                                    
                                    $cg$27 = $_4_arg.$1(null)(null)($cg$28.$1);
                                } else {
                                    $cg$27 = new $HC_1_0$Control__ST__Pure($cg$28.$1);
                                }
                                
                                return new $HC_2_1$Control__ST__Bind($cg$27, $partial_3_4$$_751_Eval__eval_58_inList_58_12_95_lam($_4_arg, $_5_arg.$1, $cg$10.$2));
                            } else {
                                
                                return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                            }
                        }
                    } else {
                        
                        if(($cg$4.$2.type === 0)) {
                            const $cg$19 = Primitives__eqv(new $HC_2_1$Prelude__List___58__58_($cg$10.$1, new $HC_2_1$Prelude__List___58__58_($_5_arg.$1, $HC_0_0$Prelude__List__Nil)));
                            let $cg$18 = null;
                            if(($cg$19.type === 0)) {
                                
                                $cg$18 = $_4_arg.$1(null)(null)($cg$19.$1);
                            } else {
                                $cg$18 = new $HC_1_0$Control__ST__Pure($cg$19.$1);
                            }
                            
                            return new $HC_2_1$Control__ST__Bind($cg$18, $partial_3_4$$_752_Eval__eval_58_inList_58_12_95_lam($_4_arg, $_5_arg.$1, $cg$10.$2));
                        } else {
                            
                            return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                        }
                    }
                } else if(($cg$10.type === 0)) {
                    
                    if(($cg$4.$2.type === 0)) {
                        return new $HC_1_0$Control__ST__Pure(false);
                    } else {
                        
                        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                    }
                } else {
                    
                    return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
                }
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
            }
        } else {
            
            return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
        }
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("case: bad syntax"));
    }
}

// Eval.eval, setCar

function Eval__eval_58_setCar_58_15($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_6_arg.type === 1)) {
        const $cg$4 = $_6_arg.$1;
        if(($cg$4.type === 3)) {
            const $cg$13 = $cg$4.$1;
            if(($cg$13.type === 1)) {
                
                const $cg$17 = $_4_arg.$3;
                return $cg$17.$4($_5_arg)($_2_arg)(new $HC_2_3$DataTypes__LispDottedList(new $HC_2_1$Prelude__List___58__58_($_7_arg, $cg$13.$2), new $JSRTS.Lazy((function(){
                    return (function(){
                        return Lists___123_cdr_95_12_125_($cg$4.$2);
                    })();
                }))));
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_2_1$DataTypes__TypeMismatch("list", $_3_arg));
            }
        } else if(($cg$4.type === 2)) {
            const $cg$7 = $cg$4.$1;
            if(($cg$7.type === 1)) {
                
                const $cg$11 = $_4_arg.$3;
                return $cg$11.$4($_5_arg)($_2_arg)(new $HC_1_2$DataTypes__LispList(new $HC_2_1$Prelude__List___58__58_($_7_arg, $cg$7.$2)));
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_2_1$DataTypes__TypeMismatch("list", $_3_arg));
            }
        } else {
            
            return $_4_arg.$1(null)(null)(new $HC_2_1$DataTypes__TypeMismatch("list", $_3_arg));
        }
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_2_1$DataTypes__TypeMismatch("list", $_3_arg));
    }
}

// Eval.eval, buildEnv

function Eval__eval_58_buildEnv_58_23($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg, $_7_arg){
    
    if(($_7_arg.type === 1)) {
        
        if(($_6_arg.type === 1)) {
            return new $HC_2_1$Control__ST__Bind(Eval__eval(null, $_4_arg, $_5_arg, $_7_arg.$1), $partial_5_6$$_756_Eval__eval_58_buildEnv_58_23_95_lam($_4_arg, $_5_arg, $_6_arg.$1, $_6_arg.$2, $_7_arg.$2));
        } else {
            
            return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("let*: bad syntax"));
        }
    } else if(($_7_arg.type === 0)) {
        
        if(($_6_arg.type === 0)) {
            return new $HC_1_0$Control__ST__Pure($HC_0_0$MkUnit);
        } else {
            
            return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("let*: bad syntax"));
        }
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("let*: bad syntax"));
    }
}

// Eval.eval, buildEnv

function Eval__eval_58_buildEnv_58_24($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        let $cg$3 = null;
        const $cg$5 = $_4_arg.$3;
        const $cg$7 = $_6_arg.$1;
        let $cg$6 = null;
        if(($cg$7.type === 1)) {
            $cg$6 = $cg$7.$1;
        } else {
            $cg$6 = new $JSRTS.Lazy((function(){
                return (function(){
                    return Eval___123_eval_95_123_125_();
                })();
            }));
        }
        
        $cg$3 = $cg$5.$5($_5_arg)($cg$6)($HC_0_13$DataTypes__LispVoid);
        return new $HC_2_1$Control__ST__Bind($cg$3, $partial_3_4$$_758_Eval__eval_58_buildEnv_58_24_95_lam($_4_arg, $_5_arg, $_6_arg.$2));
    } else if(($_6_arg.type === 0)) {
        return new $HC_1_0$Control__ST__Pure($HC_0_0$MkUnit);
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_1_6$DataTypes__Default("let*: bad syntax"));
    }
}

// Eval.eval, setRec

function Eval__eval_58_setRec_58_24($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg, $_6_arg){
    
    if(($_6_arg.type === 1)) {
        const $cg$3 = $_6_arg.$1;
        let $cg$4 = null;
        const $cg$6 = $_4_arg.$3;
        $cg$4 = $cg$6.$4($_5_arg)($cg$3.$1)($cg$3.$2);
        return new $HC_2_1$Control__ST__Bind($cg$4, $partial_3_4$$_759_Eval__eval_58_setRec_58_24_95_lam($_4_arg, $_5_arg, $_6_arg.$2));
    } else {
        return new $HC_1_0$Control__ST__Pure($HC_0_0$MkUnit);
    }
}

// Eval.eval, unpackArgs

function Eval__eval_58_unpackArgs_58_26($_0_arg, $_1_arg, $_2_arg, $_3_arg, $_4_arg, $_5_arg){
    
    if(($_5_arg.type === 1)) {
        const $cg$4 = $_5_arg.$1;
        if(($cg$4.type === 2)) {
            
            if(($_5_arg.$2.type === 0)) {
                return new $HC_1_0$Control__ST__Pure($cg$4.$1);
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_5_arg), $_5_arg));
            }
        } else {
            
            if(($_5_arg.$2.type === 0)) {
                
                return $_4_arg.$1(null)(null)(new $HC_2_1$DataTypes__TypeMismatch("list", $_5_arg.$1));
            } else {
                
                return $_4_arg.$1(null)(null)(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_5_arg), $_5_arg));
            }
        }
    } else {
        
        return $_4_arg.$1(null)(null)(new $HC_3_0$DataTypes__NumArgs(new $HC_2_1$DataTypes__MinMax(2, 2), Prelude__List__length(null, $_5_arg), $_5_arg));
    }
}

// with block in Data.String.Extra.index

function _95_Data__String__Extra__index_95_with_95_18($_0_arg, $_1_arg, $_2_arg){
    for(;;) {
        
        if(($_0_arg.type === 1)) {
            
            if($_1_arg.equals((new $JSRTS.jsbn.BigInteger(("0"))))) {
                return new $HC_1_1$Prelude__Maybe__Just($_0_arg.$1);
            } else {
                const $_5_in = $_1_arg.subtract((new $JSRTS.jsbn.BigInteger(("1"))));
                $_0_arg = $_0_arg.$2;
                $_1_arg = $_5_in;
                $_2_arg = null;
            }
        } else {
            return $HC_0_0$Prelude__Maybe__Nothing;
        }
    }
}

// with block in Prelude.Strings.unpack

function _95_Prelude__Strings__unpack_95_with_95_36($_0_arg, $_1_arg){
    
    if(($_1_arg.type === 1)) {
        let $cg$2 = null;
        if((((($_1_arg.$2 == "")) ? 1|0 : 0|0) === 0)) {
            $cg$2 = true;
        } else {
            $cg$2 = false;
        }
        
        let $cg$3 = null;
        if((Decidable__Equality__Decidable__Equality___64_Decidable__Equality__DecEq_36_Bool_58__33_decEq_58_0($cg$2, true).type === 1)) {
            $cg$3 = $HC_0_0$Prelude__Strings__StrNil;
        } else {
            $cg$3 = new $HC_2_1$Prelude__Strings__StrCons($_1_arg.$2[0], $_1_arg.$2.slice(1));
        }
        
        return new $HC_2_1$Prelude__List___58__58_($_1_arg.$1, _95_Prelude__Strings__unpack_95_with_95_36(null, $cg$3));
    } else {
        return $HC_0_0$Prelude__List__Nil;
    }
}


module.exports = {
run: function(){ return Main__run.apply(this, Array.prototype.slice.call(arguments, 0,2))}
};
}.call(this))
}).call(this,require('_process'),require("buffer").Buffer)
},{"_process":7,"buffer":4,"fs":3,"os":6}],2:[function(require,module,exports){
'use strict'

exports.byteLength = byteLength
exports.toByteArray = toByteArray
exports.fromByteArray = fromByteArray

var lookup = []
var revLookup = []
var Arr = typeof Uint8Array !== 'undefined' ? Uint8Array : Array

var code = 'ABCDEFGHIJKLMNOPQRSTUVWXYZabcdefghijklmnopqrstuvwxyz0123456789+/'
for (var i = 0, len = code.length; i < len; ++i) {
  lookup[i] = code[i]
  revLookup[code.charCodeAt(i)] = i
}

// Support decoding URL-safe base64 strings, as Node.js does.
// See: https://en.wikipedia.org/wiki/Base64#URL_applications
revLookup['-'.charCodeAt(0)] = 62
revLookup['_'.charCodeAt(0)] = 63

function getLens (b64) {
  var len = b64.length

  if (len % 4 > 0) {
    throw new Error('Invalid string. Length must be a multiple of 4')
  }

  // Trim off extra bytes after placeholder bytes are found
  // See: https://github.com/beatgammit/base64-js/issues/42
  var validLen = b64.indexOf('=')
  if (validLen === -1) validLen = len

  var placeHoldersLen = validLen === len
    ? 0
    : 4 - (validLen % 4)

  return [validLen, placeHoldersLen]
}

// base64 is 4/3 + up to two characters of the original data
function byteLength (b64) {
  var lens = getLens(b64)
  var validLen = lens[0]
  var placeHoldersLen = lens[1]
  return ((validLen + placeHoldersLen) * 3 / 4) - placeHoldersLen
}

function _byteLength (b64, validLen, placeHoldersLen) {
  return ((validLen + placeHoldersLen) * 3 / 4) - placeHoldersLen
}

function toByteArray (b64) {
  var tmp
  var lens = getLens(b64)
  var validLen = lens[0]
  var placeHoldersLen = lens[1]

  var arr = new Arr(_byteLength(b64, validLen, placeHoldersLen))

  var curByte = 0

  // if there are placeholders, only get up to the last complete 4 chars
  var len = placeHoldersLen > 0
    ? validLen - 4
    : validLen

  var i
  for (i = 0; i < len; i += 4) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 18) |
      (revLookup[b64.charCodeAt(i + 1)] << 12) |
      (revLookup[b64.charCodeAt(i + 2)] << 6) |
      revLookup[b64.charCodeAt(i + 3)]
    arr[curByte++] = (tmp >> 16) & 0xFF
    arr[curByte++] = (tmp >> 8) & 0xFF
    arr[curByte++] = tmp & 0xFF
  }

  if (placeHoldersLen === 2) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 2) |
      (revLookup[b64.charCodeAt(i + 1)] >> 4)
    arr[curByte++] = tmp & 0xFF
  }

  if (placeHoldersLen === 1) {
    tmp =
      (revLookup[b64.charCodeAt(i)] << 10) |
      (revLookup[b64.charCodeAt(i + 1)] << 4) |
      (revLookup[b64.charCodeAt(i + 2)] >> 2)
    arr[curByte++] = (tmp >> 8) & 0xFF
    arr[curByte++] = tmp & 0xFF
  }

  return arr
}

function tripletToBase64 (num) {
  return lookup[num >> 18 & 0x3F] +
    lookup[num >> 12 & 0x3F] +
    lookup[num >> 6 & 0x3F] +
    lookup[num & 0x3F]
}

function encodeChunk (uint8, start, end) {
  var tmp
  var output = []
  for (var i = start; i < end; i += 3) {
    tmp =
      ((uint8[i] << 16) & 0xFF0000) +
      ((uint8[i + 1] << 8) & 0xFF00) +
      (uint8[i + 2] & 0xFF)
    output.push(tripletToBase64(tmp))
  }
  return output.join('')
}

function fromByteArray (uint8) {
  var tmp
  var len = uint8.length
  var extraBytes = len % 3 // if we have 1 byte left, pad 2 bytes
  var parts = []
  var maxChunkLength = 16383 // must be multiple of 3

  // go through the array every three bytes, we'll deal with trailing stuff later
  for (var i = 0, len2 = len - extraBytes; i < len2; i += maxChunkLength) {
    parts.push(encodeChunk(
      uint8, i, (i + maxChunkLength) > len2 ? len2 : (i + maxChunkLength)
    ))
  }

  // pad the end with zeros, but make sure to not forget the extra bytes
  if (extraBytes === 1) {
    tmp = uint8[len - 1]
    parts.push(
      lookup[tmp >> 2] +
      lookup[(tmp << 4) & 0x3F] +
      '=='
    )
  } else if (extraBytes === 2) {
    tmp = (uint8[len - 2] << 8) + uint8[len - 1]
    parts.push(
      lookup[tmp >> 10] +
      lookup[(tmp >> 4) & 0x3F] +
      lookup[(tmp << 2) & 0x3F] +
      '='
    )
  }

  return parts.join('')
}

},{}],3:[function(require,module,exports){

},{}],4:[function(require,module,exports){
(function (Buffer){
/*!
 * The buffer module from node.js, for the browser.
 *
 * @author   Feross Aboukhadijeh <https://feross.org>
 * @license  MIT
 */
/* eslint-disable no-proto */

'use strict'

var base64 = require('base64-js')
var ieee754 = require('ieee754')
var customInspectSymbol = typeof Symbol === 'function' ? Symbol.for('nodejs.util.inspect.custom') : null

exports.Buffer = Buffer
exports.SlowBuffer = SlowBuffer
exports.INSPECT_MAX_BYTES = 50

var K_MAX_LENGTH = 0x7fffffff
exports.kMaxLength = K_MAX_LENGTH

/**
 * If `Buffer.TYPED_ARRAY_SUPPORT`:
 *   === true    Use Uint8Array implementation (fastest)
 *   === false   Print warning and recommend using `buffer` v4.x which has an Object
 *               implementation (most compatible, even IE6)
 *
 * Browsers that support typed arrays are IE 10+, Firefox 4+, Chrome 7+, Safari 5.1+,
 * Opera 11.6+, iOS 4.2+.
 *
 * We report that the browser does not support typed arrays if the are not subclassable
 * using __proto__. Firefox 4-29 lacks support for adding new properties to `Uint8Array`
 * (See: https://bugzilla.mozilla.org/show_bug.cgi?id=695438). IE 10 lacks support
 * for __proto__ and has a buggy typed array implementation.
 */
Buffer.TYPED_ARRAY_SUPPORT = typedArraySupport()

if (!Buffer.TYPED_ARRAY_SUPPORT && typeof console !== 'undefined' &&
    typeof console.error === 'function') {
  console.error(
    'This browser lacks typed array (Uint8Array) support which is required by ' +
    '`buffer` v5.x. Use `buffer` v4.x if you require old browser support.'
  )
}

function typedArraySupport () {
  // Can typed array instances can be augmented?
  try {
    var arr = new Uint8Array(1)
    var proto = { foo: function () { return 42 } }
    Object.setPrototypeOf(proto, Uint8Array.prototype)
    Object.setPrototypeOf(arr, proto)
    return arr.foo() === 42
  } catch (e) {
    return false
  }
}

Object.defineProperty(Buffer.prototype, 'parent', {
  enumerable: true,
  get: function () {
    if (!Buffer.isBuffer(this)) return undefined
    return this.buffer
  }
})

Object.defineProperty(Buffer.prototype, 'offset', {
  enumerable: true,
  get: function () {
    if (!Buffer.isBuffer(this)) return undefined
    return this.byteOffset
  }
})

function createBuffer (length) {
  if (length > K_MAX_LENGTH) {
    throw new RangeError('The value "' + length + '" is invalid for option "size"')
  }
  // Return an augmented `Uint8Array` instance
  var buf = new Uint8Array(length)
  Object.setPrototypeOf(buf, Buffer.prototype)
  return buf
}

/**
 * The Buffer constructor returns instances of `Uint8Array` that have their
 * prototype changed to `Buffer.prototype`. Furthermore, `Buffer` is a subclass of
 * `Uint8Array`, so the returned instances will have all the node `Buffer` methods
 * and the `Uint8Array` methods. Square bracket notation works as expected -- it
 * returns a single octet.
 *
 * The `Uint8Array` prototype remains unmodified.
 */

function Buffer (arg, encodingOrOffset, length) {
  // Common case.
  if (typeof arg === 'number') {
    if (typeof encodingOrOffset === 'string') {
      throw new TypeError(
        'The "string" argument must be of type string. Received type number'
      )
    }
    return allocUnsafe(arg)
  }
  return from(arg, encodingOrOffset, length)
}

// Fix subarray() in ES2016. See: https://github.com/feross/buffer/pull/97
if (typeof Symbol !== 'undefined' && Symbol.species != null &&
    Buffer[Symbol.species] === Buffer) {
  Object.defineProperty(Buffer, Symbol.species, {
    value: null,
    configurable: true,
    enumerable: false,
    writable: false
  })
}

Buffer.poolSize = 8192 // not used by this implementation

function from (value, encodingOrOffset, length) {
  if (typeof value === 'string') {
    return fromString(value, encodingOrOffset)
  }

  if (ArrayBuffer.isView(value)) {
    return fromArrayLike(value)
  }

  if (value == null) {
    throw new TypeError(
      'The first argument must be one of type string, Buffer, ArrayBuffer, Array, ' +
      'or Array-like Object. Received type ' + (typeof value)
    )
  }

  if (isInstance(value, ArrayBuffer) ||
      (value && isInstance(value.buffer, ArrayBuffer))) {
    return fromArrayBuffer(value, encodingOrOffset, length)
  }

  if (typeof value === 'number') {
    throw new TypeError(
      'The "value" argument must not be of type number. Received type number'
    )
  }

  var valueOf = value.valueOf && value.valueOf()
  if (valueOf != null && valueOf !== value) {
    return Buffer.from(valueOf, encodingOrOffset, length)
  }

  var b = fromObject(value)
  if (b) return b

  if (typeof Symbol !== 'undefined' && Symbol.toPrimitive != null &&
      typeof value[Symbol.toPrimitive] === 'function') {
    return Buffer.from(
      value[Symbol.toPrimitive]('string'), encodingOrOffset, length
    )
  }

  throw new TypeError(
    'The first argument must be one of type string, Buffer, ArrayBuffer, Array, ' +
    'or Array-like Object. Received type ' + (typeof value)
  )
}

/**
 * Functionally equivalent to Buffer(arg, encoding) but throws a TypeError
 * if value is a number.
 * Buffer.from(str[, encoding])
 * Buffer.from(array)
 * Buffer.from(buffer)
 * Buffer.from(arrayBuffer[, byteOffset[, length]])
 **/
Buffer.from = function (value, encodingOrOffset, length) {
  return from(value, encodingOrOffset, length)
}

// Note: Change prototype *after* Buffer.from is defined to workaround Chrome bug:
// https://github.com/feross/buffer/pull/148
Object.setPrototypeOf(Buffer.prototype, Uint8Array.prototype)
Object.setPrototypeOf(Buffer, Uint8Array)

function assertSize (size) {
  if (typeof size !== 'number') {
    throw new TypeError('"size" argument must be of type number')
  } else if (size < 0) {
    throw new RangeError('The value "' + size + '" is invalid for option "size"')
  }
}

function alloc (size, fill, encoding) {
  assertSize(size)
  if (size <= 0) {
    return createBuffer(size)
  }
  if (fill !== undefined) {
    // Only pay attention to encoding if it's a string. This
    // prevents accidentally sending in a number that would
    // be interpretted as a start offset.
    return typeof encoding === 'string'
      ? createBuffer(size).fill(fill, encoding)
      : createBuffer(size).fill(fill)
  }
  return createBuffer(size)
}

/**
 * Creates a new filled Buffer instance.
 * alloc(size[, fill[, encoding]])
 **/
Buffer.alloc = function (size, fill, encoding) {
  return alloc(size, fill, encoding)
}

function allocUnsafe (size) {
  assertSize(size)
  return createBuffer(size < 0 ? 0 : checked(size) | 0)
}

/**
 * Equivalent to Buffer(num), by default creates a non-zero-filled Buffer instance.
 * */
Buffer.allocUnsafe = function (size) {
  return allocUnsafe(size)
}
/**
 * Equivalent to SlowBuffer(num), by default creates a non-zero-filled Buffer instance.
 */
Buffer.allocUnsafeSlow = function (size) {
  return allocUnsafe(size)
}

function fromString (string, encoding) {
  if (typeof encoding !== 'string' || encoding === '') {
    encoding = 'utf8'
  }

  if (!Buffer.isEncoding(encoding)) {
    throw new TypeError('Unknown encoding: ' + encoding)
  }

  var length = byteLength(string, encoding) | 0
  var buf = createBuffer(length)

  var actual = buf.write(string, encoding)

  if (actual !== length) {
    // Writing a hex string, for example, that contains invalid characters will
    // cause everything after the first invalid character to be ignored. (e.g.
    // 'abxxcd' will be treated as 'ab')
    buf = buf.slice(0, actual)
  }

  return buf
}

function fromArrayLike (array) {
  var length = array.length < 0 ? 0 : checked(array.length) | 0
  var buf = createBuffer(length)
  for (var i = 0; i < length; i += 1) {
    buf[i] = array[i] & 255
  }
  return buf
}

function fromArrayBuffer (array, byteOffset, length) {
  if (byteOffset < 0 || array.byteLength < byteOffset) {
    throw new RangeError('"offset" is outside of buffer bounds')
  }

  if (array.byteLength < byteOffset + (length || 0)) {
    throw new RangeError('"length" is outside of buffer bounds')
  }

  var buf
  if (byteOffset === undefined && length === undefined) {
    buf = new Uint8Array(array)
  } else if (length === undefined) {
    buf = new Uint8Array(array, byteOffset)
  } else {
    buf = new Uint8Array(array, byteOffset, length)
  }

  // Return an augmented `Uint8Array` instance
  Object.setPrototypeOf(buf, Buffer.prototype)

  return buf
}

function fromObject (obj) {
  if (Buffer.isBuffer(obj)) {
    var len = checked(obj.length) | 0
    var buf = createBuffer(len)

    if (buf.length === 0) {
      return buf
    }

    obj.copy(buf, 0, 0, len)
    return buf
  }

  if (obj.length !== undefined) {
    if (typeof obj.length !== 'number' || numberIsNaN(obj.length)) {
      return createBuffer(0)
    }
    return fromArrayLike(obj)
  }

  if (obj.type === 'Buffer' && Array.isArray(obj.data)) {
    return fromArrayLike(obj.data)
  }
}

function checked (length) {
  // Note: cannot use `length < K_MAX_LENGTH` here because that fails when
  // length is NaN (which is otherwise coerced to zero.)
  if (length >= K_MAX_LENGTH) {
    throw new RangeError('Attempt to allocate Buffer larger than maximum ' +
                         'size: 0x' + K_MAX_LENGTH.toString(16) + ' bytes')
  }
  return length | 0
}

function SlowBuffer (length) {
  if (+length != length) { // eslint-disable-line eqeqeq
    length = 0
  }
  return Buffer.alloc(+length)
}

Buffer.isBuffer = function isBuffer (b) {
  return b != null && b._isBuffer === true &&
    b !== Buffer.prototype // so Buffer.isBuffer(Buffer.prototype) will be false
}

Buffer.compare = function compare (a, b) {
  if (isInstance(a, Uint8Array)) a = Buffer.from(a, a.offset, a.byteLength)
  if (isInstance(b, Uint8Array)) b = Buffer.from(b, b.offset, b.byteLength)
  if (!Buffer.isBuffer(a) || !Buffer.isBuffer(b)) {
    throw new TypeError(
      'The "buf1", "buf2" arguments must be one of type Buffer or Uint8Array'
    )
  }

  if (a === b) return 0

  var x = a.length
  var y = b.length

  for (var i = 0, len = Math.min(x, y); i < len; ++i) {
    if (a[i] !== b[i]) {
      x = a[i]
      y = b[i]
      break
    }
  }

  if (x < y) return -1
  if (y < x) return 1
  return 0
}

Buffer.isEncoding = function isEncoding (encoding) {
  switch (String(encoding).toLowerCase()) {
    case 'hex':
    case 'utf8':
    case 'utf-8':
    case 'ascii':
    case 'latin1':
    case 'binary':
    case 'base64':
    case 'ucs2':
    case 'ucs-2':
    case 'utf16le':
    case 'utf-16le':
      return true
    default:
      return false
  }
}

Buffer.concat = function concat (list, length) {
  if (!Array.isArray(list)) {
    throw new TypeError('"list" argument must be an Array of Buffers')
  }

  if (list.length === 0) {
    return Buffer.alloc(0)
  }

  var i
  if (length === undefined) {
    length = 0
    for (i = 0; i < list.length; ++i) {
      length += list[i].length
    }
  }

  var buffer = Buffer.allocUnsafe(length)
  var pos = 0
  for (i = 0; i < list.length; ++i) {
    var buf = list[i]
    if (isInstance(buf, Uint8Array)) {
      buf = Buffer.from(buf)
    }
    if (!Buffer.isBuffer(buf)) {
      throw new TypeError('"list" argument must be an Array of Buffers')
    }
    buf.copy(buffer, pos)
    pos += buf.length
  }
  return buffer
}

function byteLength (string, encoding) {
  if (Buffer.isBuffer(string)) {
    return string.length
  }
  if (ArrayBuffer.isView(string) || isInstance(string, ArrayBuffer)) {
    return string.byteLength
  }
  if (typeof string !== 'string') {
    throw new TypeError(
      'The "string" argument must be one of type string, Buffer, or ArrayBuffer. ' +
      'Received type ' + typeof string
    )
  }

  var len = string.length
  var mustMatch = (arguments.length > 2 && arguments[2] === true)
  if (!mustMatch && len === 0) return 0

  // Use a for loop to avoid recursion
  var loweredCase = false
  for (;;) {
    switch (encoding) {
      case 'ascii':
      case 'latin1':
      case 'binary':
        return len
      case 'utf8':
      case 'utf-8':
        return utf8ToBytes(string).length
      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return len * 2
      case 'hex':
        return len >>> 1
      case 'base64':
        return base64ToBytes(string).length
      default:
        if (loweredCase) {
          return mustMatch ? -1 : utf8ToBytes(string).length // assume utf8
        }
        encoding = ('' + encoding).toLowerCase()
        loweredCase = true
    }
  }
}
Buffer.byteLength = byteLength

function slowToString (encoding, start, end) {
  var loweredCase = false

  // No need to verify that "this.length <= MAX_UINT32" since it's a read-only
  // property of a typed array.

  // This behaves neither like String nor Uint8Array in that we set start/end
  // to their upper/lower bounds if the value passed is out of range.
  // undefined is handled specially as per ECMA-262 6th Edition,
  // Section 13.3.3.7 Runtime Semantics: KeyedBindingInitialization.
  if (start === undefined || start < 0) {
    start = 0
  }
  // Return early if start > this.length. Done here to prevent potential uint32
  // coercion fail below.
  if (start > this.length) {
    return ''
  }

  if (end === undefined || end > this.length) {
    end = this.length
  }

  if (end <= 0) {
    return ''
  }

  // Force coersion to uint32. This will also coerce falsey/NaN values to 0.
  end >>>= 0
  start >>>= 0

  if (end <= start) {
    return ''
  }

  if (!encoding) encoding = 'utf8'

  while (true) {
    switch (encoding) {
      case 'hex':
        return hexSlice(this, start, end)

      case 'utf8':
      case 'utf-8':
        return utf8Slice(this, start, end)

      case 'ascii':
        return asciiSlice(this, start, end)

      case 'latin1':
      case 'binary':
        return latin1Slice(this, start, end)

      case 'base64':
        return base64Slice(this, start, end)

      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return utf16leSlice(this, start, end)

      default:
        if (loweredCase) throw new TypeError('Unknown encoding: ' + encoding)
        encoding = (encoding + '').toLowerCase()
        loweredCase = true
    }
  }
}

// This property is used by `Buffer.isBuffer` (and the `is-buffer` npm package)
// to detect a Buffer instance. It's not possible to use `instanceof Buffer`
// reliably in a browserify context because there could be multiple different
// copies of the 'buffer' package in use. This method works even for Buffer
// instances that were created from another copy of the `buffer` package.
// See: https://github.com/feross/buffer/issues/154
Buffer.prototype._isBuffer = true

function swap (b, n, m) {
  var i = b[n]
  b[n] = b[m]
  b[m] = i
}

Buffer.prototype.swap16 = function swap16 () {
  var len = this.length
  if (len % 2 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 16-bits')
  }
  for (var i = 0; i < len; i += 2) {
    swap(this, i, i + 1)
  }
  return this
}

Buffer.prototype.swap32 = function swap32 () {
  var len = this.length
  if (len % 4 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 32-bits')
  }
  for (var i = 0; i < len; i += 4) {
    swap(this, i, i + 3)
    swap(this, i + 1, i + 2)
  }
  return this
}

Buffer.prototype.swap64 = function swap64 () {
  var len = this.length
  if (len % 8 !== 0) {
    throw new RangeError('Buffer size must be a multiple of 64-bits')
  }
  for (var i = 0; i < len; i += 8) {
    swap(this, i, i + 7)
    swap(this, i + 1, i + 6)
    swap(this, i + 2, i + 5)
    swap(this, i + 3, i + 4)
  }
  return this
}

Buffer.prototype.toString = function toString () {
  var length = this.length
  if (length === 0) return ''
  if (arguments.length === 0) return utf8Slice(this, 0, length)
  return slowToString.apply(this, arguments)
}

Buffer.prototype.toLocaleString = Buffer.prototype.toString

Buffer.prototype.equals = function equals (b) {
  if (!Buffer.isBuffer(b)) throw new TypeError('Argument must be a Buffer')
  if (this === b) return true
  return Buffer.compare(this, b) === 0
}

Buffer.prototype.inspect = function inspect () {
  var str = ''
  var max = exports.INSPECT_MAX_BYTES
  str = this.toString('hex', 0, max).replace(/(.{2})/g, '$1 ').trim()
  if (this.length > max) str += ' ... '
  return '<Buffer ' + str + '>'
}
if (customInspectSymbol) {
  Buffer.prototype[customInspectSymbol] = Buffer.prototype.inspect
}

Buffer.prototype.compare = function compare (target, start, end, thisStart, thisEnd) {
  if (isInstance(target, Uint8Array)) {
    target = Buffer.from(target, target.offset, target.byteLength)
  }
  if (!Buffer.isBuffer(target)) {
    throw new TypeError(
      'The "target" argument must be one of type Buffer or Uint8Array. ' +
      'Received type ' + (typeof target)
    )
  }

  if (start === undefined) {
    start = 0
  }
  if (end === undefined) {
    end = target ? target.length : 0
  }
  if (thisStart === undefined) {
    thisStart = 0
  }
  if (thisEnd === undefined) {
    thisEnd = this.length
  }

  if (start < 0 || end > target.length || thisStart < 0 || thisEnd > this.length) {
    throw new RangeError('out of range index')
  }

  if (thisStart >= thisEnd && start >= end) {
    return 0
  }
  if (thisStart >= thisEnd) {
    return -1
  }
  if (start >= end) {
    return 1
  }

  start >>>= 0
  end >>>= 0
  thisStart >>>= 0
  thisEnd >>>= 0

  if (this === target) return 0

  var x = thisEnd - thisStart
  var y = end - start
  var len = Math.min(x, y)

  var thisCopy = this.slice(thisStart, thisEnd)
  var targetCopy = target.slice(start, end)

  for (var i = 0; i < len; ++i) {
    if (thisCopy[i] !== targetCopy[i]) {
      x = thisCopy[i]
      y = targetCopy[i]
      break
    }
  }

  if (x < y) return -1
  if (y < x) return 1
  return 0
}

// Finds either the first index of `val` in `buffer` at offset >= `byteOffset`,
// OR the last index of `val` in `buffer` at offset <= `byteOffset`.
//
// Arguments:
// - buffer - a Buffer to search
// - val - a string, Buffer, or number
// - byteOffset - an index into `buffer`; will be clamped to an int32
// - encoding - an optional encoding, relevant is val is a string
// - dir - true for indexOf, false for lastIndexOf
function bidirectionalIndexOf (buffer, val, byteOffset, encoding, dir) {
  // Empty buffer means no match
  if (buffer.length === 0) return -1

  // Normalize byteOffset
  if (typeof byteOffset === 'string') {
    encoding = byteOffset
    byteOffset = 0
  } else if (byteOffset > 0x7fffffff) {
    byteOffset = 0x7fffffff
  } else if (byteOffset < -0x80000000) {
    byteOffset = -0x80000000
  }
  byteOffset = +byteOffset // Coerce to Number.
  if (numberIsNaN(byteOffset)) {
    // byteOffset: it it's undefined, null, NaN, "foo", etc, search whole buffer
    byteOffset = dir ? 0 : (buffer.length - 1)
  }

  // Normalize byteOffset: negative offsets start from the end of the buffer
  if (byteOffset < 0) byteOffset = buffer.length + byteOffset
  if (byteOffset >= buffer.length) {
    if (dir) return -1
    else byteOffset = buffer.length - 1
  } else if (byteOffset < 0) {
    if (dir) byteOffset = 0
    else return -1
  }

  // Normalize val
  if (typeof val === 'string') {
    val = Buffer.from(val, encoding)
  }

  // Finally, search either indexOf (if dir is true) or lastIndexOf
  if (Buffer.isBuffer(val)) {
    // Special case: looking for empty string/buffer always fails
    if (val.length === 0) {
      return -1
    }
    return arrayIndexOf(buffer, val, byteOffset, encoding, dir)
  } else if (typeof val === 'number') {
    val = val & 0xFF // Search for a byte value [0-255]
    if (typeof Uint8Array.prototype.indexOf === 'function') {
      if (dir) {
        return Uint8Array.prototype.indexOf.call(buffer, val, byteOffset)
      } else {
        return Uint8Array.prototype.lastIndexOf.call(buffer, val, byteOffset)
      }
    }
    return arrayIndexOf(buffer, [val], byteOffset, encoding, dir)
  }

  throw new TypeError('val must be string, number or Buffer')
}

function arrayIndexOf (arr, val, byteOffset, encoding, dir) {
  var indexSize = 1
  var arrLength = arr.length
  var valLength = val.length

  if (encoding !== undefined) {
    encoding = String(encoding).toLowerCase()
    if (encoding === 'ucs2' || encoding === 'ucs-2' ||
        encoding === 'utf16le' || encoding === 'utf-16le') {
      if (arr.length < 2 || val.length < 2) {
        return -1
      }
      indexSize = 2
      arrLength /= 2
      valLength /= 2
      byteOffset /= 2
    }
  }

  function read (buf, i) {
    if (indexSize === 1) {
      return buf[i]
    } else {
      return buf.readUInt16BE(i * indexSize)
    }
  }

  var i
  if (dir) {
    var foundIndex = -1
    for (i = byteOffset; i < arrLength; i++) {
      if (read(arr, i) === read(val, foundIndex === -1 ? 0 : i - foundIndex)) {
        if (foundIndex === -1) foundIndex = i
        if (i - foundIndex + 1 === valLength) return foundIndex * indexSize
      } else {
        if (foundIndex !== -1) i -= i - foundIndex
        foundIndex = -1
      }
    }
  } else {
    if (byteOffset + valLength > arrLength) byteOffset = arrLength - valLength
    for (i = byteOffset; i >= 0; i--) {
      var found = true
      for (var j = 0; j < valLength; j++) {
        if (read(arr, i + j) !== read(val, j)) {
          found = false
          break
        }
      }
      if (found) return i
    }
  }

  return -1
}

Buffer.prototype.includes = function includes (val, byteOffset, encoding) {
  return this.indexOf(val, byteOffset, encoding) !== -1
}

Buffer.prototype.indexOf = function indexOf (val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, true)
}

Buffer.prototype.lastIndexOf = function lastIndexOf (val, byteOffset, encoding) {
  return bidirectionalIndexOf(this, val, byteOffset, encoding, false)
}

function hexWrite (buf, string, offset, length) {
  offset = Number(offset) || 0
  var remaining = buf.length - offset
  if (!length) {
    length = remaining
  } else {
    length = Number(length)
    if (length > remaining) {
      length = remaining
    }
  }

  var strLen = string.length

  if (length > strLen / 2) {
    length = strLen / 2
  }
  for (var i = 0; i < length; ++i) {
    var parsed = parseInt(string.substr(i * 2, 2), 16)
    if (numberIsNaN(parsed)) return i
    buf[offset + i] = parsed
  }
  return i
}

function utf8Write (buf, string, offset, length) {
  return blitBuffer(utf8ToBytes(string, buf.length - offset), buf, offset, length)
}

function asciiWrite (buf, string, offset, length) {
  return blitBuffer(asciiToBytes(string), buf, offset, length)
}

function latin1Write (buf, string, offset, length) {
  return asciiWrite(buf, string, offset, length)
}

function base64Write (buf, string, offset, length) {
  return blitBuffer(base64ToBytes(string), buf, offset, length)
}

function ucs2Write (buf, string, offset, length) {
  return blitBuffer(utf16leToBytes(string, buf.length - offset), buf, offset, length)
}

Buffer.prototype.write = function write (string, offset, length, encoding) {
  // Buffer#write(string)
  if (offset === undefined) {
    encoding = 'utf8'
    length = this.length
    offset = 0
  // Buffer#write(string, encoding)
  } else if (length === undefined && typeof offset === 'string') {
    encoding = offset
    length = this.length
    offset = 0
  // Buffer#write(string, offset[, length][, encoding])
  } else if (isFinite(offset)) {
    offset = offset >>> 0
    if (isFinite(length)) {
      length = length >>> 0
      if (encoding === undefined) encoding = 'utf8'
    } else {
      encoding = length
      length = undefined
    }
  } else {
    throw new Error(
      'Buffer.write(string, encoding, offset[, length]) is no longer supported'
    )
  }

  var remaining = this.length - offset
  if (length === undefined || length > remaining) length = remaining

  if ((string.length > 0 && (length < 0 || offset < 0)) || offset > this.length) {
    throw new RangeError('Attempt to write outside buffer bounds')
  }

  if (!encoding) encoding = 'utf8'

  var loweredCase = false
  for (;;) {
    switch (encoding) {
      case 'hex':
        return hexWrite(this, string, offset, length)

      case 'utf8':
      case 'utf-8':
        return utf8Write(this, string, offset, length)

      case 'ascii':
        return asciiWrite(this, string, offset, length)

      case 'latin1':
      case 'binary':
        return latin1Write(this, string, offset, length)

      case 'base64':
        // Warning: maxLength not taken into account in base64Write
        return base64Write(this, string, offset, length)

      case 'ucs2':
      case 'ucs-2':
      case 'utf16le':
      case 'utf-16le':
        return ucs2Write(this, string, offset, length)

      default:
        if (loweredCase) throw new TypeError('Unknown encoding: ' + encoding)
        encoding = ('' + encoding).toLowerCase()
        loweredCase = true
    }
  }
}

Buffer.prototype.toJSON = function toJSON () {
  return {
    type: 'Buffer',
    data: Array.prototype.slice.call(this._arr || this, 0)
  }
}

function base64Slice (buf, start, end) {
  if (start === 0 && end === buf.length) {
    return base64.fromByteArray(buf)
  } else {
    return base64.fromByteArray(buf.slice(start, end))
  }
}

function utf8Slice (buf, start, end) {
  end = Math.min(buf.length, end)
  var res = []

  var i = start
  while (i < end) {
    var firstByte = buf[i]
    var codePoint = null
    var bytesPerSequence = (firstByte > 0xEF) ? 4
      : (firstByte > 0xDF) ? 3
        : (firstByte > 0xBF) ? 2
          : 1

    if (i + bytesPerSequence <= end) {
      var secondByte, thirdByte, fourthByte, tempCodePoint

      switch (bytesPerSequence) {
        case 1:
          if (firstByte < 0x80) {
            codePoint = firstByte
          }
          break
        case 2:
          secondByte = buf[i + 1]
          if ((secondByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0x1F) << 0x6 | (secondByte & 0x3F)
            if (tempCodePoint > 0x7F) {
              codePoint = tempCodePoint
            }
          }
          break
        case 3:
          secondByte = buf[i + 1]
          thirdByte = buf[i + 2]
          if ((secondByte & 0xC0) === 0x80 && (thirdByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0xF) << 0xC | (secondByte & 0x3F) << 0x6 | (thirdByte & 0x3F)
            if (tempCodePoint > 0x7FF && (tempCodePoint < 0xD800 || tempCodePoint > 0xDFFF)) {
              codePoint = tempCodePoint
            }
          }
          break
        case 4:
          secondByte = buf[i + 1]
          thirdByte = buf[i + 2]
          fourthByte = buf[i + 3]
          if ((secondByte & 0xC0) === 0x80 && (thirdByte & 0xC0) === 0x80 && (fourthByte & 0xC0) === 0x80) {
            tempCodePoint = (firstByte & 0xF) << 0x12 | (secondByte & 0x3F) << 0xC | (thirdByte & 0x3F) << 0x6 | (fourthByte & 0x3F)
            if (tempCodePoint > 0xFFFF && tempCodePoint < 0x110000) {
              codePoint = tempCodePoint
            }
          }
      }
    }

    if (codePoint === null) {
      // we did not generate a valid codePoint so insert a
      // replacement char (U+FFFD) and advance only 1 byte
      codePoint = 0xFFFD
      bytesPerSequence = 1
    } else if (codePoint > 0xFFFF) {
      // encode to utf16 (surrogate pair dance)
      codePoint -= 0x10000
      res.push(codePoint >>> 10 & 0x3FF | 0xD800)
      codePoint = 0xDC00 | codePoint & 0x3FF
    }

    res.push(codePoint)
    i += bytesPerSequence
  }

  return decodeCodePointsArray(res)
}

// Based on http://stackoverflow.com/a/22747272/680742, the browser with
// the lowest limit is Chrome, with 0x10000 args.
// We go 1 magnitude less, for safety
var MAX_ARGUMENTS_LENGTH = 0x1000

function decodeCodePointsArray (codePoints) {
  var len = codePoints.length
  if (len <= MAX_ARGUMENTS_LENGTH) {
    return String.fromCharCode.apply(String, codePoints) // avoid extra slice()
  }

  // Decode in chunks to avoid "call stack size exceeded".
  var res = ''
  var i = 0
  while (i < len) {
    res += String.fromCharCode.apply(
      String,
      codePoints.slice(i, i += MAX_ARGUMENTS_LENGTH)
    )
  }
  return res
}

function asciiSlice (buf, start, end) {
  var ret = ''
  end = Math.min(buf.length, end)

  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i] & 0x7F)
  }
  return ret
}

function latin1Slice (buf, start, end) {
  var ret = ''
  end = Math.min(buf.length, end)

  for (var i = start; i < end; ++i) {
    ret += String.fromCharCode(buf[i])
  }
  return ret
}

function hexSlice (buf, start, end) {
  var len = buf.length

  if (!start || start < 0) start = 0
  if (!end || end < 0 || end > len) end = len

  var out = ''
  for (var i = start; i < end; ++i) {
    out += toHex(buf[i])
  }
  return out
}

function utf16leSlice (buf, start, end) {
  var bytes = buf.slice(start, end)
  var res = ''
  for (var i = 0; i < bytes.length; i += 2) {
    res += String.fromCharCode(bytes[i] + (bytes[i + 1] * 256))
  }
  return res
}

Buffer.prototype.slice = function slice (start, end) {
  var len = this.length
  start = ~~start
  end = end === undefined ? len : ~~end

  if (start < 0) {
    start += len
    if (start < 0) start = 0
  } else if (start > len) {
    start = len
  }

  if (end < 0) {
    end += len
    if (end < 0) end = 0
  } else if (end > len) {
    end = len
  }

  if (end < start) end = start

  var newBuf = this.subarray(start, end)
  // Return an augmented `Uint8Array` instance
  Object.setPrototypeOf(newBuf, Buffer.prototype)

  return newBuf
}

/*
 * Need to make sure that buffer isn't trying to write out of bounds.
 */
function checkOffset (offset, ext, length) {
  if ((offset % 1) !== 0 || offset < 0) throw new RangeError('offset is not uint')
  if (offset + ext > length) throw new RangeError('Trying to access beyond buffer length')
}

Buffer.prototype.readUIntLE = function readUIntLE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var val = this[offset]
  var mul = 1
  var i = 0
  while (++i < byteLength && (mul *= 0x100)) {
    val += this[offset + i] * mul
  }

  return val
}

Buffer.prototype.readUIntBE = function readUIntBE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    checkOffset(offset, byteLength, this.length)
  }

  var val = this[offset + --byteLength]
  var mul = 1
  while (byteLength > 0 && (mul *= 0x100)) {
    val += this[offset + --byteLength] * mul
  }

  return val
}

Buffer.prototype.readUInt8 = function readUInt8 (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 1, this.length)
  return this[offset]
}

Buffer.prototype.readUInt16LE = function readUInt16LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  return this[offset] | (this[offset + 1] << 8)
}

Buffer.prototype.readUInt16BE = function readUInt16BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  return (this[offset] << 8) | this[offset + 1]
}

Buffer.prototype.readUInt32LE = function readUInt32LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return ((this[offset]) |
      (this[offset + 1] << 8) |
      (this[offset + 2] << 16)) +
      (this[offset + 3] * 0x1000000)
}

Buffer.prototype.readUInt32BE = function readUInt32BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset] * 0x1000000) +
    ((this[offset + 1] << 16) |
    (this[offset + 2] << 8) |
    this[offset + 3])
}

Buffer.prototype.readIntLE = function readIntLE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var val = this[offset]
  var mul = 1
  var i = 0
  while (++i < byteLength && (mul *= 0x100)) {
    val += this[offset + i] * mul
  }
  mul *= 0x80

  if (val >= mul) val -= Math.pow(2, 8 * byteLength)

  return val
}

Buffer.prototype.readIntBE = function readIntBE (offset, byteLength, noAssert) {
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) checkOffset(offset, byteLength, this.length)

  var i = byteLength
  var mul = 1
  var val = this[offset + --i]
  while (i > 0 && (mul *= 0x100)) {
    val += this[offset + --i] * mul
  }
  mul *= 0x80

  if (val >= mul) val -= Math.pow(2, 8 * byteLength)

  return val
}

Buffer.prototype.readInt8 = function readInt8 (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 1, this.length)
  if (!(this[offset] & 0x80)) return (this[offset])
  return ((0xff - this[offset] + 1) * -1)
}

Buffer.prototype.readInt16LE = function readInt16LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  var val = this[offset] | (this[offset + 1] << 8)
  return (val & 0x8000) ? val | 0xFFFF0000 : val
}

Buffer.prototype.readInt16BE = function readInt16BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 2, this.length)
  var val = this[offset + 1] | (this[offset] << 8)
  return (val & 0x8000) ? val | 0xFFFF0000 : val
}

Buffer.prototype.readInt32LE = function readInt32LE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset]) |
    (this[offset + 1] << 8) |
    (this[offset + 2] << 16) |
    (this[offset + 3] << 24)
}

Buffer.prototype.readInt32BE = function readInt32BE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)

  return (this[offset] << 24) |
    (this[offset + 1] << 16) |
    (this[offset + 2] << 8) |
    (this[offset + 3])
}

Buffer.prototype.readFloatLE = function readFloatLE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)
  return ieee754.read(this, offset, true, 23, 4)
}

Buffer.prototype.readFloatBE = function readFloatBE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 4, this.length)
  return ieee754.read(this, offset, false, 23, 4)
}

Buffer.prototype.readDoubleLE = function readDoubleLE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 8, this.length)
  return ieee754.read(this, offset, true, 52, 8)
}

Buffer.prototype.readDoubleBE = function readDoubleBE (offset, noAssert) {
  offset = offset >>> 0
  if (!noAssert) checkOffset(offset, 8, this.length)
  return ieee754.read(this, offset, false, 52, 8)
}

function checkInt (buf, value, offset, ext, max, min) {
  if (!Buffer.isBuffer(buf)) throw new TypeError('"buffer" argument must be a Buffer instance')
  if (value > max || value < min) throw new RangeError('"value" argument is out of bounds')
  if (offset + ext > buf.length) throw new RangeError('Index out of range')
}

Buffer.prototype.writeUIntLE = function writeUIntLE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength) - 1
    checkInt(this, value, offset, byteLength, maxBytes, 0)
  }

  var mul = 1
  var i = 0
  this[offset] = value & 0xFF
  while (++i < byteLength && (mul *= 0x100)) {
    this[offset + i] = (value / mul) & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeUIntBE = function writeUIntBE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  byteLength = byteLength >>> 0
  if (!noAssert) {
    var maxBytes = Math.pow(2, 8 * byteLength) - 1
    checkInt(this, value, offset, byteLength, maxBytes, 0)
  }

  var i = byteLength - 1
  var mul = 1
  this[offset + i] = value & 0xFF
  while (--i >= 0 && (mul *= 0x100)) {
    this[offset + i] = (value / mul) & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeUInt8 = function writeUInt8 (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 1, 0xff, 0)
  this[offset] = (value & 0xff)
  return offset + 1
}

Buffer.prototype.writeUInt16LE = function writeUInt16LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0xffff, 0)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  return offset + 2
}

Buffer.prototype.writeUInt16BE = function writeUInt16BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0xffff, 0)
  this[offset] = (value >>> 8)
  this[offset + 1] = (value & 0xff)
  return offset + 2
}

Buffer.prototype.writeUInt32LE = function writeUInt32LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0xffffffff, 0)
  this[offset + 3] = (value >>> 24)
  this[offset + 2] = (value >>> 16)
  this[offset + 1] = (value >>> 8)
  this[offset] = (value & 0xff)
  return offset + 4
}

Buffer.prototype.writeUInt32BE = function writeUInt32BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0xffffffff, 0)
  this[offset] = (value >>> 24)
  this[offset + 1] = (value >>> 16)
  this[offset + 2] = (value >>> 8)
  this[offset + 3] = (value & 0xff)
  return offset + 4
}

Buffer.prototype.writeIntLE = function writeIntLE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    var limit = Math.pow(2, (8 * byteLength) - 1)

    checkInt(this, value, offset, byteLength, limit - 1, -limit)
  }

  var i = 0
  var mul = 1
  var sub = 0
  this[offset] = value & 0xFF
  while (++i < byteLength && (mul *= 0x100)) {
    if (value < 0 && sub === 0 && this[offset + i - 1] !== 0) {
      sub = 1
    }
    this[offset + i] = ((value / mul) >> 0) - sub & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeIntBE = function writeIntBE (value, offset, byteLength, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    var limit = Math.pow(2, (8 * byteLength) - 1)

    checkInt(this, value, offset, byteLength, limit - 1, -limit)
  }

  var i = byteLength - 1
  var mul = 1
  var sub = 0
  this[offset + i] = value & 0xFF
  while (--i >= 0 && (mul *= 0x100)) {
    if (value < 0 && sub === 0 && this[offset + i + 1] !== 0) {
      sub = 1
    }
    this[offset + i] = ((value / mul) >> 0) - sub & 0xFF
  }

  return offset + byteLength
}

Buffer.prototype.writeInt8 = function writeInt8 (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 1, 0x7f, -0x80)
  if (value < 0) value = 0xff + value + 1
  this[offset] = (value & 0xff)
  return offset + 1
}

Buffer.prototype.writeInt16LE = function writeInt16LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0x7fff, -0x8000)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  return offset + 2
}

Buffer.prototype.writeInt16BE = function writeInt16BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 2, 0x7fff, -0x8000)
  this[offset] = (value >>> 8)
  this[offset + 1] = (value & 0xff)
  return offset + 2
}

Buffer.prototype.writeInt32LE = function writeInt32LE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0x7fffffff, -0x80000000)
  this[offset] = (value & 0xff)
  this[offset + 1] = (value >>> 8)
  this[offset + 2] = (value >>> 16)
  this[offset + 3] = (value >>> 24)
  return offset + 4
}

Buffer.prototype.writeInt32BE = function writeInt32BE (value, offset, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) checkInt(this, value, offset, 4, 0x7fffffff, -0x80000000)
  if (value < 0) value = 0xffffffff + value + 1
  this[offset] = (value >>> 24)
  this[offset + 1] = (value >>> 16)
  this[offset + 2] = (value >>> 8)
  this[offset + 3] = (value & 0xff)
  return offset + 4
}

function checkIEEE754 (buf, value, offset, ext, max, min) {
  if (offset + ext > buf.length) throw new RangeError('Index out of range')
  if (offset < 0) throw new RangeError('Index out of range')
}

function writeFloat (buf, value, offset, littleEndian, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 4, 3.4028234663852886e+38, -3.4028234663852886e+38)
  }
  ieee754.write(buf, value, offset, littleEndian, 23, 4)
  return offset + 4
}

Buffer.prototype.writeFloatLE = function writeFloatLE (value, offset, noAssert) {
  return writeFloat(this, value, offset, true, noAssert)
}

Buffer.prototype.writeFloatBE = function writeFloatBE (value, offset, noAssert) {
  return writeFloat(this, value, offset, false, noAssert)
}

function writeDouble (buf, value, offset, littleEndian, noAssert) {
  value = +value
  offset = offset >>> 0
  if (!noAssert) {
    checkIEEE754(buf, value, offset, 8, 1.7976931348623157E+308, -1.7976931348623157E+308)
  }
  ieee754.write(buf, value, offset, littleEndian, 52, 8)
  return offset + 8
}

Buffer.prototype.writeDoubleLE = function writeDoubleLE (value, offset, noAssert) {
  return writeDouble(this, value, offset, true, noAssert)
}

Buffer.prototype.writeDoubleBE = function writeDoubleBE (value, offset, noAssert) {
  return writeDouble(this, value, offset, false, noAssert)
}

// copy(targetBuffer, targetStart=0, sourceStart=0, sourceEnd=buffer.length)
Buffer.prototype.copy = function copy (target, targetStart, start, end) {
  if (!Buffer.isBuffer(target)) throw new TypeError('argument should be a Buffer')
  if (!start) start = 0
  if (!end && end !== 0) end = this.length
  if (targetStart >= target.length) targetStart = target.length
  if (!targetStart) targetStart = 0
  if (end > 0 && end < start) end = start

  // Copy 0 bytes; we're done
  if (end === start) return 0
  if (target.length === 0 || this.length === 0) return 0

  // Fatal error conditions
  if (targetStart < 0) {
    throw new RangeError('targetStart out of bounds')
  }
  if (start < 0 || start >= this.length) throw new RangeError('Index out of range')
  if (end < 0) throw new RangeError('sourceEnd out of bounds')

  // Are we oob?
  if (end > this.length) end = this.length
  if (target.length - targetStart < end - start) {
    end = target.length - targetStart + start
  }

  var len = end - start

  if (this === target && typeof Uint8Array.prototype.copyWithin === 'function') {
    // Use built-in when available, missing from IE11
    this.copyWithin(targetStart, start, end)
  } else if (this === target && start < targetStart && targetStart < end) {
    // descending copy from end
    for (var i = len - 1; i >= 0; --i) {
      target[i + targetStart] = this[i + start]
    }
  } else {
    Uint8Array.prototype.set.call(
      target,
      this.subarray(start, end),
      targetStart
    )
  }

  return len
}

// Usage:
//    buffer.fill(number[, offset[, end]])
//    buffer.fill(buffer[, offset[, end]])
//    buffer.fill(string[, offset[, end]][, encoding])
Buffer.prototype.fill = function fill (val, start, end, encoding) {
  // Handle string cases:
  if (typeof val === 'string') {
    if (typeof start === 'string') {
      encoding = start
      start = 0
      end = this.length
    } else if (typeof end === 'string') {
      encoding = end
      end = this.length
    }
    if (encoding !== undefined && typeof encoding !== 'string') {
      throw new TypeError('encoding must be a string')
    }
    if (typeof encoding === 'string' && !Buffer.isEncoding(encoding)) {
      throw new TypeError('Unknown encoding: ' + encoding)
    }
    if (val.length === 1) {
      var code = val.charCodeAt(0)
      if ((encoding === 'utf8' && code < 128) ||
          encoding === 'latin1') {
        // Fast path: If `val` fits into a single byte, use that numeric value.
        val = code
      }
    }
  } else if (typeof val === 'number') {
    val = val & 255
  }

  // Invalid ranges are not set to a default, so can range check early.
  if (start < 0 || this.length < start || this.length < end) {
    throw new RangeError('Out of range index')
  }

  if (end <= start) {
    return this
  }

  start = start >>> 0
  end = end === undefined ? this.length : end >>> 0

  if (!val) val = 0

  var i
  if (typeof val === 'number') {
    for (i = start; i < end; ++i) {
      this[i] = val
    }
  } else {
    var bytes = Buffer.isBuffer(val)
      ? val
      : Buffer.from(val, encoding)
    var len = bytes.length
    if (len === 0) {
      throw new TypeError('The value "' + val +
        '" is invalid for argument "value"')
    }
    for (i = 0; i < end - start; ++i) {
      this[i + start] = bytes[i % len]
    }
  }

  return this
}

// HELPER FUNCTIONS
// ================

var INVALID_BASE64_RE = /[^+/0-9A-Za-z-_]/g

function base64clean (str) {
  // Node takes equal signs as end of the Base64 encoding
  str = str.split('=')[0]
  // Node strips out invalid characters like \n and \t from the string, base64-js does not
  str = str.trim().replace(INVALID_BASE64_RE, '')
  // Node converts strings with length < 2 to ''
  if (str.length < 2) return ''
  // Node allows for non-padded base64 strings (missing trailing ===), base64-js does not
  while (str.length % 4 !== 0) {
    str = str + '='
  }
  return str
}

function toHex (n) {
  if (n < 16) return '0' + n.toString(16)
  return n.toString(16)
}

function utf8ToBytes (string, units) {
  units = units || Infinity
  var codePoint
  var length = string.length
  var leadSurrogate = null
  var bytes = []

  for (var i = 0; i < length; ++i) {
    codePoint = string.charCodeAt(i)

    // is surrogate component
    if (codePoint > 0xD7FF && codePoint < 0xE000) {
      // last char was a lead
      if (!leadSurrogate) {
        // no lead yet
        if (codePoint > 0xDBFF) {
          // unexpected trail
          if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
          continue
        } else if (i + 1 === length) {
          // unpaired lead
          if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
          continue
        }

        // valid lead
        leadSurrogate = codePoint

        continue
      }

      // 2 leads in a row
      if (codePoint < 0xDC00) {
        if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
        leadSurrogate = codePoint
        continue
      }

      // valid surrogate pair
      codePoint = (leadSurrogate - 0xD800 << 10 | codePoint - 0xDC00) + 0x10000
    } else if (leadSurrogate) {
      // valid bmp char, but last char was a lead
      if ((units -= 3) > -1) bytes.push(0xEF, 0xBF, 0xBD)
    }

    leadSurrogate = null

    // encode utf8
    if (codePoint < 0x80) {
      if ((units -= 1) < 0) break
      bytes.push(codePoint)
    } else if (codePoint < 0x800) {
      if ((units -= 2) < 0) break
      bytes.push(
        codePoint >> 0x6 | 0xC0,
        codePoint & 0x3F | 0x80
      )
    } else if (codePoint < 0x10000) {
      if ((units -= 3) < 0) break
      bytes.push(
        codePoint >> 0xC | 0xE0,
        codePoint >> 0x6 & 0x3F | 0x80,
        codePoint & 0x3F | 0x80
      )
    } else if (codePoint < 0x110000) {
      if ((units -= 4) < 0) break
      bytes.push(
        codePoint >> 0x12 | 0xF0,
        codePoint >> 0xC & 0x3F | 0x80,
        codePoint >> 0x6 & 0x3F | 0x80,
        codePoint & 0x3F | 0x80
      )
    } else {
      throw new Error('Invalid code point')
    }
  }

  return bytes
}

function asciiToBytes (str) {
  var byteArray = []
  for (var i = 0; i < str.length; ++i) {
    // Node's code seems to be doing this and not & 0x7F..
    byteArray.push(str.charCodeAt(i) & 0xFF)
  }
  return byteArray
}

function utf16leToBytes (str, units) {
  var c, hi, lo
  var byteArray = []
  for (var i = 0; i < str.length; ++i) {
    if ((units -= 2) < 0) break

    c = str.charCodeAt(i)
    hi = c >> 8
    lo = c % 256
    byteArray.push(lo)
    byteArray.push(hi)
  }

  return byteArray
}

function base64ToBytes (str) {
  return base64.toByteArray(base64clean(str))
}

function blitBuffer (src, dst, offset, length) {
  for (var i = 0; i < length; ++i) {
    if ((i + offset >= dst.length) || (i >= src.length)) break
    dst[i + offset] = src[i]
  }
  return i
}

// ArrayBuffer or Uint8Array objects from other contexts (i.e. iframes) do not pass
// the `instanceof` check but they should be treated as of that type.
// See: https://github.com/feross/buffer/issues/166
function isInstance (obj, type) {
  return obj instanceof type ||
    (obj != null && obj.constructor != null && obj.constructor.name != null &&
      obj.constructor.name === type.name)
}
function numberIsNaN (obj) {
  // For IE11 support
  return obj !== obj // eslint-disable-line no-self-compare
}

}).call(this,require("buffer").Buffer)
},{"base64-js":2,"buffer":4,"ieee754":5}],5:[function(require,module,exports){
exports.read = function (buffer, offset, isLE, mLen, nBytes) {
  var e, m
  var eLen = (nBytes * 8) - mLen - 1
  var eMax = (1 << eLen) - 1
  var eBias = eMax >> 1
  var nBits = -7
  var i = isLE ? (nBytes - 1) : 0
  var d = isLE ? -1 : 1
  var s = buffer[offset + i]

  i += d

  e = s & ((1 << (-nBits)) - 1)
  s >>= (-nBits)
  nBits += eLen
  for (; nBits > 0; e = (e * 256) + buffer[offset + i], i += d, nBits -= 8) {}

  m = e & ((1 << (-nBits)) - 1)
  e >>= (-nBits)
  nBits += mLen
  for (; nBits > 0; m = (m * 256) + buffer[offset + i], i += d, nBits -= 8) {}

  if (e === 0) {
    e = 1 - eBias
  } else if (e === eMax) {
    return m ? NaN : ((s ? -1 : 1) * Infinity)
  } else {
    m = m + Math.pow(2, mLen)
    e = e - eBias
  }
  return (s ? -1 : 1) * m * Math.pow(2, e - mLen)
}

exports.write = function (buffer, value, offset, isLE, mLen, nBytes) {
  var e, m, c
  var eLen = (nBytes * 8) - mLen - 1
  var eMax = (1 << eLen) - 1
  var eBias = eMax >> 1
  var rt = (mLen === 23 ? Math.pow(2, -24) - Math.pow(2, -77) : 0)
  var i = isLE ? 0 : (nBytes - 1)
  var d = isLE ? 1 : -1
  var s = value < 0 || (value === 0 && 1 / value < 0) ? 1 : 0

  value = Math.abs(value)

  if (isNaN(value) || value === Infinity) {
    m = isNaN(value) ? 1 : 0
    e = eMax
  } else {
    e = Math.floor(Math.log(value) / Math.LN2)
    if (value * (c = Math.pow(2, -e)) < 1) {
      e--
      c *= 2
    }
    if (e + eBias >= 1) {
      value += rt / c
    } else {
      value += rt * Math.pow(2, 1 - eBias)
    }
    if (value * c >= 2) {
      e++
      c /= 2
    }

    if (e + eBias >= eMax) {
      m = 0
      e = eMax
    } else if (e + eBias >= 1) {
      m = ((value * c) - 1) * Math.pow(2, mLen)
      e = e + eBias
    } else {
      m = value * Math.pow(2, eBias - 1) * Math.pow(2, mLen)
      e = 0
    }
  }

  for (; mLen >= 8; buffer[offset + i] = m & 0xff, i += d, m /= 256, mLen -= 8) {}

  e = (e << mLen) | m
  eLen += mLen
  for (; eLen > 0; buffer[offset + i] = e & 0xff, i += d, e /= 256, eLen -= 8) {}

  buffer[offset + i - d] |= s * 128
}

},{}],6:[function(require,module,exports){
exports.endianness = function () { return 'LE' };

exports.hostname = function () {
    if (typeof location !== 'undefined') {
        return location.hostname
    }
    else return '';
};

exports.loadavg = function () { return [] };

exports.uptime = function () { return 0 };

exports.freemem = function () {
    return Number.MAX_VALUE;
};

exports.totalmem = function () {
    return Number.MAX_VALUE;
};

exports.cpus = function () { return [] };

exports.type = function () { return 'Browser' };

exports.release = function () {
    if (typeof navigator !== 'undefined') {
        return navigator.appVersion;
    }
    return '';
};

exports.networkInterfaces
= exports.getNetworkInterfaces
= function () { return {} };

exports.arch = function () { return 'javascript' };

exports.platform = function () { return 'browser' };

exports.tmpdir = exports.tmpDir = function () {
    return '/tmp';
};

exports.EOL = '\n';

exports.homedir = function () {
	return '/'
};

},{}],7:[function(require,module,exports){
// shim for using process in browser
var process = module.exports = {};

// cached from whatever global is present so that test runners that stub it
// don't break things.  But we need to wrap it in a try catch in case it is
// wrapped in strict mode code which doesn't define any globals.  It's inside a
// function because try/catches deoptimize in certain engines.

var cachedSetTimeout;
var cachedClearTimeout;

function defaultSetTimout() {
    throw new Error('setTimeout has not been defined');
}
function defaultClearTimeout () {
    throw new Error('clearTimeout has not been defined');
}
(function () {
    try {
        if (typeof setTimeout === 'function') {
            cachedSetTimeout = setTimeout;
        } else {
            cachedSetTimeout = defaultSetTimout;
        }
    } catch (e) {
        cachedSetTimeout = defaultSetTimout;
    }
    try {
        if (typeof clearTimeout === 'function') {
            cachedClearTimeout = clearTimeout;
        } else {
            cachedClearTimeout = defaultClearTimeout;
        }
    } catch (e) {
        cachedClearTimeout = defaultClearTimeout;
    }
} ())
function runTimeout(fun) {
    if (cachedSetTimeout === setTimeout) {
        //normal enviroments in sane situations
        return setTimeout(fun, 0);
    }
    // if setTimeout wasn't available but was latter defined
    if ((cachedSetTimeout === defaultSetTimout || !cachedSetTimeout) && setTimeout) {
        cachedSetTimeout = setTimeout;
        return setTimeout(fun, 0);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedSetTimeout(fun, 0);
    } catch(e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't trust the global object when called normally
            return cachedSetTimeout.call(null, fun, 0);
        } catch(e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error
            return cachedSetTimeout.call(this, fun, 0);
        }
    }


}
function runClearTimeout(marker) {
    if (cachedClearTimeout === clearTimeout) {
        //normal enviroments in sane situations
        return clearTimeout(marker);
    }
    // if clearTimeout wasn't available but was latter defined
    if ((cachedClearTimeout === defaultClearTimeout || !cachedClearTimeout) && clearTimeout) {
        cachedClearTimeout = clearTimeout;
        return clearTimeout(marker);
    }
    try {
        // when when somebody has screwed with setTimeout but no I.E. maddness
        return cachedClearTimeout(marker);
    } catch (e){
        try {
            // When we are in I.E. but the script has been evaled so I.E. doesn't  trust the global object when called normally
            return cachedClearTimeout.call(null, marker);
        } catch (e){
            // same as above but when it's a version of I.E. that must have the global object for 'this', hopfully our context correct otherwise it will throw a global error.
            // Some versions of I.E. have different rules for clearTimeout vs setTimeout
            return cachedClearTimeout.call(this, marker);
        }
    }



}
var queue = [];
var draining = false;
var currentQueue;
var queueIndex = -1;

function cleanUpNextTick() {
    if (!draining || !currentQueue) {
        return;
    }
    draining = false;
    if (currentQueue.length) {
        queue = currentQueue.concat(queue);
    } else {
        queueIndex = -1;
    }
    if (queue.length) {
        drainQueue();
    }
}

function drainQueue() {
    if (draining) {
        return;
    }
    var timeout = runTimeout(cleanUpNextTick);
    draining = true;

    var len = queue.length;
    while(len) {
        currentQueue = queue;
        queue = [];
        while (++queueIndex < len) {
            if (currentQueue) {
                currentQueue[queueIndex].run();
            }
        }
        queueIndex = -1;
        len = queue.length;
    }
    currentQueue = null;
    draining = false;
    runClearTimeout(timeout);
}

process.nextTick = function (fun) {
    var args = new Array(arguments.length - 1);
    if (arguments.length > 1) {
        for (var i = 1; i < arguments.length; i++) {
            args[i - 1] = arguments[i];
        }
    }
    queue.push(new Item(fun, args));
    if (queue.length === 1 && !draining) {
        runTimeout(drainQueue);
    }
};

// v8 likes predictible objects
function Item(fun, array) {
    this.fun = fun;
    this.array = array;
}
Item.prototype.run = function () {
    this.fun.apply(null, this.array);
};
process.title = 'browser';
process.browser = true;
process.env = {};
process.argv = [];
process.version = ''; // empty string to avoid regexp issues
process.versions = {};

function noop() {}

process.on = noop;
process.addListener = noop;
process.once = noop;
process.off = noop;
process.removeListener = noop;
process.removeAllListeners = noop;
process.emit = noop;
process.prependListener = noop;
process.prependOnceListener = noop;

process.listeners = function (name) { return [] }

process.binding = function (name) {
    throw new Error('process.binding is not supported');
};

process.cwd = function () { return '/' };
process.chdir = function (dir) {
    throw new Error('process.chdir is not supported');
};
process.umask = function() { return 0; };

},{}]},{},[1])(1)
});
