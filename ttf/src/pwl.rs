use crate::point::*;
use crate::ttf_num::TTFNum;
use crate::UndercutDescriptor;

use std::cmp::Ordering;
use std::ops;

const BUCKET_SIZE: usize = 8;

#[derive(Clone, Debug, PartialEq)]
#[cfg_attr(feature = "serde-1", derive(Deserialize, Serialize))]
pub struct PwlTTF<T> {
    points: Vec<Point<T>>,
    min: Option<T>,
    max: Option<T>,
    period: [T; 2],
    buckets: Vec<usize>,
    bucket_shift: usize,
}

impl<T: TTFNum> PwlTTF<T> {
    pub fn from_x_and_y(x: Vec<T>, y: Vec<T>) -> Self {
        assert_eq!(x.len(), y.len());
        let period = [x[0], x[x.len() - 1]];
        let mut ttf = Self::with_capacity(period, x.len());
        for (x, y) in x.into_iter().zip(y.into_iter()) {
            ttf.append_point(Point { x, y });
        }
        ttf.setup_buckets();
        ttf
    }

    pub fn from_breakpoints(points: Vec<(T, T)>) -> Self {
        let period = [points[0].0, points[points.len() - 1].0];
        let mut ttf = Self::with_capacity(period, points.len());
        for (x, y) in points.into_iter() {
            ttf.append_point(Point { x, y });
        }
        ttf.setup_buckets();
        ttf
    }

    fn with_capacity(period: [T; 2], capacity: usize) -> Self {
        PwlTTF {
            points: Vec::with_capacity(capacity),
            min: None,
            max: None,
            period,
            buckets: Vec::with_capacity(BUCKET_SIZE),
            bucket_shift: 0,
        }
    }

    fn iter(&self) -> impl Iterator<Item = &Point<T>> {
        self.points.iter()
    }

    fn double_iter(&self) -> impl Iterator<Item = (&Point<T>, &Point<T>)> {
        self.points.iter().zip(self.points[1..].iter())
    }

    fn append_point(&mut self, p: Point<T>) {
        debug_assert!(p.y >= T::zero());
        debug_assert!(self.is_empty() || self.points.last().unwrap().x.approx_le(&p.x));
        debug_assert!(!self.is_empty() || p.x == self.period[0]);
        debug_assert!(p.x >= self.period[0]);
        debug_assert!(p.x <= self.period[1]);
        self.update_min_max(p.y);
        if let Some(last_point) = self.points.last_mut() {
            if last_point.x.approx_eq(&p.x) {
                // The point to add has the same x as the last point added.
                if last_point.y.approx_eq(&p.y) {
                    // Do not try to add the same point again.
                    return;
                }
                let new_x = last_point.x.max(&p.x) + T::margin();
                last_point.x = last_point.x.min(&p.x);
                debug_assert!(last_point.x < new_x);
                self.points.push(Point { x: new_x, y: p.y });
                return;
            }
            debug_assert!(last_point.x < p.x);
        }
        if self.len() > 1
            && rotation(
                &self.points[self.len() - 2],
                &self.points[self.len() - 1],
                &p,
            ) == Rotation::Colinear
        {
            // The new point is colinear with the two previous points.
            // The new point replaces the last one.
            *self.points.last_mut().unwrap() = p;
            return;
        }
        debug_assert!(self.is_empty() || self.points.last().unwrap().x < p.x);
        self.points.push(p);
    }

    fn update_min_max(&mut self, y: T) {
        if self.min.is_none() || y < self.min.unwrap() {
            self.min = Some(y);
        } else if self.max.is_none() || y > self.max.unwrap() {
            self.max = Some(y);
        }
    }

    fn is_fifo(&self) -> bool {
        for (p, q) in self.double_iter() {
            if (q.x + q.y).approx_lt(&(p.x + p.y)) {
                return false;
            }
        }
        true
    }

    pub fn is_empty(&self) -> bool {
        self.points.is_empty()
    }

    pub fn len(&self) -> usize {
        self.points.len()
    }

    pub fn middle_departure_time(&self) -> T {
        self.period[0].average(&self.period[1])
    }

    pub fn get_min(&self) -> T {
        debug_assert!(self.min.is_some());
        debug_assert!(self.min.unwrap().approx_eq(
            &self
                .iter()
                .map(|&p| p.y)
                .min_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap()
        ));
        self.min.unwrap()
    }

    pub fn get_max(&self) -> T {
        debug_assert!(self.max.is_some());
        debug_assert!(self.max.unwrap().approx_eq(
            &self
                .iter()
                .map(|&p| p.y)
                .max_by(|a, b| a.partial_cmp(b).unwrap())
                .unwrap()
        ));
        self.max.unwrap()
    }

    pub fn is_cst(&self) -> bool {
        self.len() == 1
    }

    pub fn get_cst_value(&self) -> T {
        debug_assert!(self.is_cst());
        self[0].y
    }

    fn get_bucket(&self, x: T) -> usize {
        debug_assert!(x >= self.period[0]);
        let bucket = x.to_usize() >> self.bucket_shift;
        if bucket > 0 {
            bucket - 1
        } else {
            debug_assert!(bucket < self.buckets.len());
            bucket
        }
    }

    pub fn eval(&self, x: T) -> T {
        debug_assert!(!self.is_empty());
        debug_assert!(x >= self.period[0], "{:?} < {:?}", x, self.period[0]);
        if x.approx_ge(&self.period[1]) {
            return self[self.len() - 1].y;
        }
        let bucket = self.get_bucket(x);
        debug_assert!(self.buckets[bucket] < self.len());
        debug_assert!(self.buckets[bucket] == 0 || self[self.buckets[bucket] - 1].x.approx_le(&x));
        for i in self.buckets[bucket]..self.len() {
            if x.approx_le(&self[i].x) {
                if x.approx_eq(&self[i].x) {
                    return self[i].y;
                }
                debug_assert!(i > 0);
                debug_assert!(self[i - 1].x.approx_le(&x));
                debug_assert!(x.approx_le(&self[i].x));
                return linear_interp(self[i - 1], self[i], x);
            }
        }
        debug_assert!(self.points.last().unwrap().x.approx_le(&x));
        // We assume that travel time stays constant after the last breakpoint.
        self.points.last().unwrap().y
    }

    fn first_index_with_x_ge(&self, x: T) -> usize {
        debug_assert!(!self.is_empty());
        debug_assert!(x >= self.period[0] && x <= self.period[1]);
        let bucket = self.get_bucket(x);
        let index = self.buckets[bucket];
        debug_assert!(index < self.len());
        debug_assert!(index == 0 || self[index - 1].x.approx_le(&x));
        for i in self.buckets[bucket]..self.len() {
            if self[i].x >= x {
                debug_assert!(i == 0 || self[i - 1].x < x);
                return i;
            }
        }
        debug_assert!(self[self.len() - 1].x < x);
        self.len()
    }

    fn setup_buckets(&mut self) {
        let period_len = (self.period[1] - self.period[0]).to_usize();
        self.bucket_shift = std::mem::size_of::<usize>() * 8 - 1;
        let n = period_len * BUCKET_SIZE / self.len();
        // Compute the position of the most significant bit of n.
        while n & (1 << self.bucket_shift) == 0 {
            self.bucket_shift -= 1;
        }

        let n_buckets = std::cmp::max(1, period_len >> self.bucket_shift);
        self.buckets = vec![0; n_buckets];

        let mut bucket = 0;
        for (i, x) in self.points.iter().map(|p| p.x).enumerate() {
            while self.get_bucket(x) >= bucket {
                debug_assert!(bucket < n_buckets);
                self.buckets[bucket] = i;
                bucket += 1;
            }
        }
        while bucket < n_buckets {
            self.buckets[bucket] = self.len() - 1;
            bucket += 1;
        }
    }

    pub fn add(&mut self, c: T) {
        debug_assert!(!self.is_empty());
        self.min = Some(self.get_min() + c);
        self.max = Some(self.get_max() + c);
        for p in self.points.iter_mut() {
            p.y = p.y + c;
        }
    }

    #[allow(dead_code)]
    fn dbg_check_link(&self, f: &Self, g: &Self) -> bool {
        let mut x_values = Vec::with_capacity(f.len() + g.len() + self.len());
        for &Point { x, y: _ } in g.iter() {
            x_values.push(x);
        }
        for &Point { x, y: _ } in f.iter() {
            x_values.push(x);
        }
        for &Point { x, y: _ } in self.iter() {
            x_values.push(x);
        }

        for x in x_values {
            let result = self.eval(x);
            let f_res = f.eval(x);
            let expected_result = f_res + g.eval(f_res);
            debug_assert!(
                result.approx_eq(&expected_result),
                "h(x) =  {:?} != f(x) + g(f(x)) = {:?} + {:?} = {:?}",
                result,
                f_res,
                g.eval(f_res),
                expected_result
            );
        }

        true
    }

    fn dbg_check_min(&self, f: &Self, g: &Self) -> bool {
        let mut x_values = Vec::with_capacity(f.len() + g.len() + self.len());
        for &Point { x, y: _ } in g.iter() {
            x_values.push(x);
        }
        for &Point { x, y: _ } in f.iter() {
            x_values.push(x);
        }
        for &Point { x, y: _ } in self.iter() {
            x_values.push(x);
        }

        for x in x_values {
            let result = self.eval(x);
            let expected_result = f.eval(x).min(&g.eval(x));
            debug_assert!(
                result.approx_eq(&expected_result),
                "h(x) = {:?} != min(f(x), g(x)) = min({:?}, {:?}) = {:?}",
                self.eval(x),
                f.eval(x),
                g.eval(x),
                f.eval(x).min(&g.eval(x))
            );
        }

        true
    }
}

impl<T> ops::Index<usize> for PwlTTF<T> {
    type Output = Point<T>;

    fn index(&self, i: usize) -> &Self::Output {
        &self.points[std::cmp::min(i, self.points.len() - 1)]
    }
}

fn linear_interp<T: TTFNum>(p: Point<T>, q: Point<T>, x: T) -> T {
    debug_assert!(p.x.approx_le(&x));
    debug_assert!(x.approx_le(&q.x));
    let m = (q.y - p.y) / (q.x - p.x);
    m * (x - p.x) + p.y
}

fn inv_linear_interp<T: TTFNum>(p: Point<T>, q: Point<T>, z: T) -> T {
    debug_assert!((p.x + p.y).approx_le(&z));
    debug_assert!(z.approx_le(&(q.x + q.y)));
    let m = (q.x - p.x) / (q.x + q.y - p.x - p.y);
    m * (z - p.x - p.y) + p.x
}

pub fn link<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> PwlTTF<T> {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert!(f.is_fifo());
    debug_assert_eq!(f.period, g.period);
    debug_assert!(f[0].x.approx_eq(&g[0].x));

    let mut h = PwlTTF::with_capacity(f.period, f.len() + g.len());
    let mut i = g.first_index_with_x_ge(f.eval(T::zero()));
    let mut j = 0;

    while i < g.len() && j < f.len() {
        let (x, y);
        if g[i].x.approx_eq(&(f[j].x + f[j].y)) {
            x = f[j].x;
            y = f[j].y + g[i].y;
            i += 1;
            j += 1;
        } else if g[i].x < f[j].x + f[j].y {
            x = inv_linear_interp(f[j - 1], f[j], g[i].x);
            y = g[i].x + g[i].y - x;
            i += 1;
        } else {
            x = f[j].x;
            y = f[j].y + linear_interp(g[i - 1], g[i], f[j].x + f[j].y);
            j += 1;
        }
        h.append_point(Point { x, y });
    }
    for j in j..f.len() {
        let x = f[j].x;
        let y = f[j].y + g[g.len() - 1].y;
        h.append_point(Point { x, y });
    }
    for i in i..g.len() {
        let x = g[i].x - f[f.len() - 1].y;
        let y = f[f.len() - 1].y + g[i].y;
        h.append_point(Point { x, y });
    }
    h.points.shrink_to_fit();
    h.setup_buckets();
    // debug_assert!(h.dbg_check_link(f, g));
    h
}

pub fn link_cst_before<T: TTFNum>(g: &PwlTTF<T>, c: T) -> PwlTTF<T> {
    debug_assert!(!g.is_empty());

    let mut h = PwlTTF::with_capacity(g.period, g.len());
    let i = g.first_index_with_x_ge(c);

    if i == g.len() {
        // g ends before first g.period[0] + c.
        let p = Point {
            x: h.period[0],
            y: c + g[0].x,
        };
        h.append_point(p);
    }

    for i in i..g.len() {
        let p = Point {
            x: g[i].x - c,
            y: g[i].y + c,
        };
        debug_assert!(p.x >= h.period[0]);
        if p.x > h.period[0] && h.is_empty() {
            // Add first point.
            let p0 = Point {
                x: h.period[0],
                y: c + g.eval(c),
            };
            h.append_point(p0);
        }
        h.append_point(p);
    }

    h.points.shrink_to_fit();
    h.setup_buckets();
    h
}

pub fn merge<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> (PwlTTF<T>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());
    debug_assert!(!g.is_empty());
    debug_assert_eq!(f.period, g.period);

    let mut descr = UndercutDescriptor::default();

    if f.get_max().approx_lt(&g.get_min()) {
        descr.f_undercuts_strictly = true;
        return (f.clone(), descr);
    } else if g.get_max().approx_lt(&f.get_min()) {
        descr.g_undercuts_strictly = true;
        return (g.clone(), descr);
    }

    let mut h = PwlTTF::with_capacity(f.period, f.len() + g.len());

    debug_assert_eq!(f[0].x, h.period[0]);
    debug_assert_eq!(g[0].x, h.period[0]);
    h.append_point(Point {
        x: h.period[0],
        y: f[0].y.min(&g[0].y),
    });

    let mut i = 1;
    let mut j = 1;

    while i < f.len() && j < g.len() {
        if intersect(&f[i - 1], &f[i], &g[j - 1], &g[j]) {
            let p = intersection_point(&f[i - 1], &f[i], &g[j - 1], &g[j]);
            h.append_point(p);
            descr.f_undercuts_strictly = true;
            descr.g_undercuts_strictly = true;
        }

        if f[i].x.approx_eq(&g[j].x) {
            if f[i].y.approx_eq(&g[j].y) {
                h.append_point(f[i]);

                if rotation(&g[j - 1], &f[i - 1], &f[i]) == Rotation::CounterClockwise
                    || rotation(&f[i], &f[i + 1], &g[j + 1]) == Rotation::CounterClockwise
                {
                    descr.f_undercuts_strictly = true;
                }

                if rotation(&g[j - 1], &f[i - 1], &f[i]) == Rotation::Clockwise
                    || rotation(&f[i], &f[i + 1], &g[j + 1]) == Rotation::Clockwise
                {
                    descr.g_undercuts_strictly = true;
                }
            } else if f[i].y < g[j].y {
                h.append_point(f[i]);
                descr.f_undercuts_strictly = true;
            } else {
                h.append_point(g[j]);
                descr.g_undercuts_strictly = true;
            }
            i += 1;
            j += 1;
        } else if f[i].x < g[j].x {
            match rotation(&g[j - 1], &f[i], &g[j]) {
                Rotation::CounterClockwise => {
                    descr.f_undercuts_strictly = true;
                    h.append_point(f[i]);
                }
                Rotation::Colinear => {
                    if rotation(&g[j - 1], &f[i - 1], &f[i]) == Rotation::CounterClockwise
                        || rotation(&f[i], &f[i + 1], &g[j]) == Rotation::CounterClockwise
                    {
                        descr.f_undercuts_strictly = true;
                        h.append_point(f[i]);
                    }
                    if rotation(&g[j - 1], &f[i - 1], &f[i]) == Rotation::Clockwise
                        || rotation(&f[i], &f[i + 1], &g[j]) == Rotation::Clockwise
                    {
                        descr.g_undercuts_strictly = true;
                    }
                }
                Rotation::Clockwise => (),
            }
            i += 1;
        } else {
            match rotation(&f[i - 1], &g[j], &f[i]) {
                Rotation::CounterClockwise => {
                    descr.g_undercuts_strictly = true;
                    h.append_point(g[j]);
                }
                Rotation::Colinear => {
                    if rotation(&f[i - 1], &g[j - 1], &g[j]) == Rotation::CounterClockwise
                        || rotation(&g[j], &g[j + 1], &f[i]) == Rotation::CounterClockwise
                    {
                        descr.g_undercuts_strictly = true;
                        h.append_point(g[j]);
                    }
                    if rotation(&f[i - 1], &g[j - 1], &g[j]) == Rotation::Clockwise
                        || rotation(&g[j], &g[j + 1], &f[i]) == Rotation::Clockwise
                    {
                        descr.g_undercuts_strictly = true;
                    }
                }
                Rotation::Clockwise => (),
            }
            j += 1;
        }
    }

    let last_y_from_other = if i < f.len() {
        g[g.len() - 1].y
    } else {
        f[f.len() - 1].y
    };
    for i in i..f.len() {
        if f[i].y.approx_eq(&last_y_from_other) {
            h.append_point(f[i]);
        } else if f[i].y < last_y_from_other {
            if f[i - 1].y > last_y_from_other {
                let p = intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other);
                h.append_point(p);
            }
            descr.f_undercuts_strictly = true;
            h.append_point(f[i]);
        } else if f[i - 1].y < last_y_from_other {
            let p = intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other);
            descr.g_undercuts_strictly = true;
            h.append_point(p);
        }
    }
    for j in j..g.len() {
        if g[j].y.approx_eq(&last_y_from_other) {
            h.append_point(g[j]);
        } else if g[j].y < last_y_from_other {
            if g[j - 1].y > last_y_from_other {
                let p = intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other);
                h.append_point(p);
            }
            descr.g_undercuts_strictly = true;
            h.append_point(g[j]);
        } else if g[j - 1].y < last_y_from_other {
            let p = intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other);
            descr.f_undercuts_strictly = true;
            h.append_point(p);
        }
    }

    debug_assert!(!h.is_empty());
    h.points.shrink_to_fit();
    h.setup_buckets();
    debug_assert!(h.dbg_check_min(f, g));
    (h, descr)
}

pub fn merge_cst<T: TTFNum>(f: &PwlTTF<T>, c: T) -> (PwlTTF<T>, UndercutDescriptor) {
    debug_assert!(!f.is_empty());

    let mut descr = UndercutDescriptor::default();

    if c.approx_lt(&f.get_max()) {
        descr.g_undercuts_strictly = true;
    }
    if f.get_min().approx_lt(&c) {
        descr.f_undercuts_strictly = true;
    }

    let mut h = PwlTTF::with_capacity(f.period, 2 * f.len());

    if c.approx_le(&f.get_min()) {
        let p = Point {
            x: h.period[0],
            y: c,
        };
        h.append_point(p);
        h.points.shrink_to_fit();
        h.setup_buckets();
        return (h, descr);
    }

    debug_assert_eq!(f[0].x, h.period[0]);
    h.append_point(Point {
        x: h.period[0],
        y: f[0].y.min(&c),
    });

    for i in 1..f.len() {
        if f[i].y.approx_eq(&c) {
            if f[i - 1].y.approx_lt(&c) || (i < f.len() - 1 && f[i + 1].y.approx_lt(&c)) {
                h.append_point(Point { x: f[i].x, y: c });
            }
        } else if f[i].y < c {
            if c.approx_lt(&f[i - 1].y) {
                let p = intersection_point_horizontal(&f[i - 1], &f[i], c);
                h.append_point(p);
            }
            h.append_point(f[i]);
        } else if f[i - 1].y.approx_lt(&c) {
            let p = intersection_point_horizontal(&f[i - 1], &f[i], c);
            h.append_point(p);
        }
    }

    debug_assert!(!h.is_empty());
    h.points.shrink_to_fit();
    h.setup_buckets();
    (h, descr)
}

pub fn analyze_relative_position<T: TTFNum>(f: &PwlTTF<T>, g: &PwlTTF<T>) -> Vec<(T, Ordering)> {
    debug_assert_eq!(f.period, g.period);

    if f.get_max().approx_le(&g.get_min()) {
        return vec![(f.period[0], Ordering::Less)];
    }
    if g.get_max().approx_le(&f.get_min()) {
        return vec![(g.period[0], Ordering::Greater)];
    }

    let mut results = Vec::with_capacity(f.len() + g.len());
    let mut i = 1;
    let mut j = 1;
    debug_assert_eq!(f[0].x, f.period[0]);
    debug_assert_eq!(g[0].x, g.period[0]);
    let mut rel_pos = if f[0].y.approx_eq(&g[0].y) {
        Ordering::Equal
    } else if f[0].y < g[0].y {
        Ordering::Less
    } else {
        Ordering::Greater
    };
    if rel_pos != Ordering::Equal {
        results.push((f.period[0], rel_pos));
    }

    while i < f.len() && j < g.len() {
        let mut increment_i = false;
        let mut increment_j = false;
        let old_rel_pos = rel_pos;
        if f[i].x.approx_eq(&g[j].x) {
            increment_i = true;
            increment_j = true;
            if g[j].y.approx_lt(&f[i].y) {
                rel_pos = Ordering::Greater;
            } else if f[i].y.approx_lt(&g[j].y) {
                rel_pos = Ordering::Less;
            }
        } else if f[i].x < g[j].x {
            increment_i = true;
            match rotation(&g[j - 1], &f[i], &g[j]) {
                Rotation::Clockwise => {
                    rel_pos = Ordering::Greater;
                }
                Rotation::CounterClockwise => {
                    rel_pos = Ordering::Less;
                }
                Rotation::Colinear => (),
            }
        } else {
            increment_j = true;
            match rotation(&f[i - 1], &g[j], &f[i]) {
                Rotation::Clockwise => {
                    rel_pos = Ordering::Less;
                }
                Rotation::CounterClockwise => {
                    rel_pos = Ordering::Greater;
                }
                Rotation::Colinear => (),
            }
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&g[j - 1].x) && f[i - 1].y.approx_eq(&g[j - 1].y) {
                f[i - 1].x
            } else if rotation(&g[j - 1], &f[i - 1], &g[j]) == Rotation::Colinear
                && rotation(&f[i - 1], &g[j - 1], &f[i]) == Rotation::Colinear
            {
                f[i - 1].x.max(&g[j - 1].x)
            } else if rotation(&g[j - 1], &f[i - 1], &g[j]) == Rotation::Colinear {
                f[i - 1].x
            } else if rotation(&f[i - 1], &g[j - 1], &f[i]) == Rotation::Colinear {
                g[j - 1].x
            } else {
                intersection_point(&f[i - 1], &f[i], &g[j - 1], &g[j]).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }

        if increment_i {
            i += 1;
        }
        if increment_j {
            j += 1
        }
    }

    let last_y_from_other = if i < f.len() {
        g[g.len() - 1].y
    } else {
        f[f.len() - 1].y
    };
    for i in i..f.len() {
        let old_rel_pos = rel_pos;
        if f[i].y.approx_lt(&last_y_from_other) {
            rel_pos = Ordering::Less;
        } else if f[i].y.approx_gt(&last_y_from_other) {
            rel_pos = Ordering::Greater;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&last_y_from_other) {
                f[i - 1].x
            } else {
                intersection_point_horizontal(&f[i - 1], &f[i], last_y_from_other).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }
    for j in j..g.len() {
        let old_rel_pos = rel_pos;
        if g[j].y.approx_lt(&last_y_from_other) {
            rel_pos = Ordering::Greater;
        } else if g[j].y.approx_gt(&last_y_from_other) {
            rel_pos = Ordering::Less;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if g[j - 1].x.approx_eq(&last_y_from_other) {
                g[j - 1].x
            } else {
                intersection_point_horizontal(&g[j - 1], &g[j], last_y_from_other).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.period[0], Ordering::Less));
    }

    debug_assert_eq!(results[0].0, f.period[0]);

    results
}

pub fn analyze_relative_position_to_cst<T: TTFNum>(f: &PwlTTF<T>, c: T) -> Vec<(T, Ordering)> {
    if f.get_max().approx_le(&c) {
        return vec![(f.period[0], Ordering::Less)];
    }
    if c.approx_le(&f.get_min()) {
        return vec![(f.period[0], Ordering::Greater)];
    }

    let mut results = Vec::with_capacity(2 * f.len());
    debug_assert_eq!(f[0].x, f.period[0]);
    let mut rel_pos = if f[0].y.approx_eq(&c) {
        Ordering::Equal
    } else if f[0].y < c {
        Ordering::Less
    } else {
        Ordering::Greater
    };
    if rel_pos != Ordering::Equal {
        results.push((f.period[0], rel_pos));
    }

    for i in 0..f.len() {
        let old_rel_pos = rel_pos;
        if f[i].y.approx_lt(&c) {
            rel_pos = Ordering::Less;
        } else if f[i].y.approx_gt(&c) {
            rel_pos = Ordering::Greater;
        }

        if old_rel_pos != rel_pos {
            // Find `x` where the relative positioning switched.
            let x = if f[i - 1].x.approx_eq(&c) {
                f[i - 1].x
            } else {
                intersection_point_horizontal(&f[i - 1], &f[i], c).x
            };
            debug_assert!(x >= f.period[0]);
            debug_assert!(x <= f.period[1]);
            debug_assert!(results.is_empty() || results.last().unwrap().0 < x);
            if results.is_empty() {
                // f and g were equal at the beginning of the period.
                results.push((f.period[0], rel_pos));
            } else {
                results.push((x, rel_pos));
            }
        }
    }

    if results.is_empty() {
        results.push((f.period[0], Ordering::Greater));
    }

    debug_assert_eq!(results[0].0, f.period[0]);

    results
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn piecewise_test() {
        let breakpoints = vec![(-10., 15.), (0., 20.), (10., 5.)];
        let ttf = PwlTTF::from_breakpoints(breakpoints);
        assert_eq!(ttf.eval(-10.), 15.);
        assert_eq!(ttf.eval(0.), 20.);
        assert_eq!(ttf.eval(10.), 5.);
        assert_eq!(ttf.eval(-5.), 17.5);
    }

    #[test]
    #[should_panic]
    fn piecewise_panic_test1() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let ttf = PwlTTF::from_breakpoints(breakpoints);
        ttf.eval(-15.);
    }

    #[test]
    #[should_panic]
    fn piecewise_panic_test2() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let ttf = PwlTTF::from_breakpoints(breakpoints);
        ttf.eval(15.);
    }

    #[test]
    #[should_panic]
    fn piecewise_panic_test3() {
        let breakpoints = vec![(-10., 5.), (0., 10.), (10., -5.)];
        let ttf = PwlTTF::from_breakpoints(breakpoints);
        ttf.eval(f64::NAN);
    }
}
