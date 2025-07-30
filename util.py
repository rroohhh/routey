#!/usr/bin/env python3

class EqDefaultDict:
    def __init__(self, gen):
        self._gen = gen
        self._items = []

    def __getitem__(self, searched_key):
        for (key, value) in self._items:
            if key == searched_key:
                return value
        else:
            self._items.append((searched_key, self._gen()))
            return self._items[-1][1]
