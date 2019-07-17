from __future__ import print_function
def print(*s):
	pass
"""
(C) Copyright 2018 CERN and University of Manchester.
This software is distributed under the terms of the GNU General Public Licence version 3 (GPL Version 3), copied verbatim in the file "COPYING".
In applying this licence, CERN does not waive the privileges and immunities granted to it by virtue of its status as an Intergovernmental Organization or submit itself to any jurisdiction.

Author: Joshua Dawes - CERN, University of Manchester - joshua.dawes@cern.ch
"""
"""
This module contains the classes necessary to represent a parse tree wrt a grammar.
We use this to build parse trees of paths wrt grammars derived from SCFGs.
"""

from construction import CFGVertex, CFGEdge
import pprint

class ParseTreeVertex(object):
	"""
	Class to represent vertices of a parse tree.
	"""
	def __init__(self, symbol, children=[]):
		self._symbol = symbol
		self._children = []

	def has_terminal_symbol(self):
		return type(self._symbol) is CFGEdge

	def add_child(self, child):
		self._children.append(child)

class ParseTree(object):
	"""
	Class to represent a parse tree.
	"""
	def __init__(self, path=None, rules=None, starting_vertex=None, empty=False):
		if not(empty):
			self._root_vertex = ParseTreeVertex(starting_vertex)
			self._vertices = [self._root_vertex]
			self._rules = rules
			self._target_path = path
			self._path_progress = []
			self._all_paths = []
			self.expand_vertex(self._root_vertex)
			self.compute_all_paths(self._root_vertex, [self._root_vertex._symbol])
		else:
			# this is the case where we're using a set of paths through
			# other parse trees to build a single parse tree,
			# rather than building a parse tree from a path from an SCFG.
			self._root_vertex = ParseTreeVertex(starting_vertex)
			self._vertices = [self._root_vertex]
			self._all_paths = []

	def expand_vertex(self, vertex):
		"""
		Given a vertex in the parse tree, expand it using self._rules
		to generate its child nodes
		"""
		# get the rules associated with the symbol held by this vertex
		rules = self._rules[vertex._symbol]
		if len(rules) > 1:
			progress_length = len(self._path_progress)
			first_relevant_symbol = self._target_path[progress_length]
			rule_to_use = rules[0]
			for rule in rules:
				if rule[0] == first_relevant_symbol:
					rule_to_use = rule
		else:
			rule_to_use = rules[0]

		for symbol in rule_to_use:
			child_vertex = ParseTreeVertex(symbol)
			vertex.add_child(child_vertex)
			self._vertices.append(child_vertex)
			if type(symbol) is CFGEdge:
				# terminal symbol
				self._path_progress.append(symbol)
				if self._path_progress == self._target_path:
					print("target path generated early")
					return False
			elif type(symbol) is CFGVertex:
				# non-terminal symbol
				result = self.expand_vertex(child_vertex)
				if result == False:
					return False

	def leaves_to_left_right_sequence(self, curr, symbol_sequence):
		"""
		Recursively construct the sequence of symbols by going left to right in traversal.
		"""
		for child in curr._children:
			if len(child._children) == 0:
				# we have a leaf
				symbol_sequence.append(child._symbol)
			else:
				# recurse
				self.leaves_to_left_right_sequence(child, symbol_sequence)


	def compute_all_paths(self, vertex, current_path=[]):
		"""
		Given vertex and current_path, find all children, copy current_path for each and recurse on them.
		As soon as we encounter a leaf (type CFGEdge), we add current_path to self._all_paths.
		"""
		for child in vertex._children:
			current_path_copy = [e for e in current_path]
			current_path_copy.append(child._symbol)
			if len(child._children) == 0:
				self._all_paths.append(current_path_copy)
			else:
				self.compute_all_paths(child, current_path_copy)

	def intersect(self, other_trees):
		"""
		Find the set of all paths through self, then
		traverse the same paths through every tree in other_trees as long as there is agreement.
		Whenever there isn't agreement, the path being followed is trimmed.
		The intersection is then any tree (we take self) with all vertices not covered
		by the resulting set of paths thrown away.
		"""
		# get a copy of the set of all paths - we need a copy because we'll modify the paths

		all_paths_copy = []
		for path in self._all_paths:
			all_paths_copy.append([e for e in path])

		for tree in other_trees:
			for (n, path) in enumerate(all_paths_copy):
				print("following path %s" % path)
				# follow the path through tree
				# as soon as we can't follow it any further, cut the rest off the path
				current_parse_tree_vertex = tree._root_vertex
				trim_index = 0
				for (path_index, parse_tree_vertex) in enumerate(path):
					if path_index+1 < len(path):
						# there is still a next element in the path,
						# look for child vertices that match it
						found = False
						for (child_index, child) in enumerate(current_parse_tree_vertex._children):
							if path[path_index+1] == child._symbol:
								current_parse_tree_vertex = child
								found = True

						if not(found):
							# we found a disagreement, so trim this path
							trim_index = path_index+1
							print("disagreement found at position %i" % trim_index)
							break
					else:
						# do nothing - we exhausted the path without encountering disagreement
						print("path exhausted without disagreement")
						trim_index = len(path)

				all_paths_copy[n] = all_paths_copy[n][:trim_index]

			print("trimmed paths:")
			unique_paths = []
			# form unique set
			for path in all_paths_copy:
				if not(path in unique_paths):
					unique_paths.append(path)

			all_paths_copy = unique_paths

		# there will still be paths that are subpaths of others - for now, leave it
		# but it may prove more efficient to remove redundant paths now.

		pprint.pprint(all_paths_copy)

		new_parse_tree = self.build_parse_tree_from_paths(all_paths_copy)

		# now, follow all the paths through the original parse tree (self), copying
		# the vertices covered by the paths into a new parse tree

		"""new_parse_tree = ParseTree(vertex_set=[v for v in self._vertices])
		symbols_to_keep = []
		for path in all_paths_copy:
			symbols_to_keep += path
		symbols_to_keep = list(set(symbols_to_keep))

		print("symbols to keep")
		print(symbols_to_keep)

		print("parse tree vertices", map(lambda vertex : vertex._symbol, new_parse_tree._vertices))

		vertices_to_remove = []

		for vertex in new_parse_tree._vertices:
			child_vertices_to_remove = []
			for child in vertex._children:
				if not(child._symbol in symbols_to_keep):
					child_vertices_to_remove.append(child)
			vertex._children = list(set(vertex._children) - set(child_vertices_to_remove))
			if not(vertex._symbol in symbols_to_keep):
				vertices_to_remove.append(vertex)

		new_parse_tree._vertices = list(set(new_parse_tree._vertices) - set(vertices_to_remove))

		print(len(new_parse_tree._vertices))

		print("new parse tree vertices:", map(lambda vertex : vertex._symbol, new_parse_tree._vertices))"""

		return new_parse_tree

	def build_parse_tree_from_paths(self, paths):
		"""
		Given a list of paths (probably derived from intersecting two trees), build
		the parse tree that is described by those paths.
		"""

		# initialise an empty parse tree
		new_parse_tree = ParseTree(empty=True, starting_vertex=paths[0][0])

		# iterate through the paths
		for path in paths:
			# try to follow the path through the empty parse tree
			# if the next symbol isn't found, construct a new parse tree vertex with that symbol
			# start from the root of the parse tree
			curr = new_parse_tree._root_vertex
			# iterate through the elements of the path, leaving out the starting vertex
			for el in path[1:]:
				child_exists = False
				for child in curr._children:
					if child._symbol == el:
						child_exists = True

				if child_exists:
					curr = child
				else:
					new_parse_tree_vertex = ParseTreeVertex(el)
					curr._children.append(new_parse_tree_vertex)
					new_parse_tree._vertices.append(new_parse_tree_vertex)
					curr = new_parse_tree_vertex

		new_parse_tree.compute_all_paths(
			new_parse_tree._root_vertex,
			[new_parse_tree._root_vertex._symbol]
		)

		return new_parse_tree

	def get_parameter_paths(self, curr, current_path, path_parameters):
		"""
		If this is an intersected parse tree, we are interested in finding the list of leaves that are vertices (hence, path parameters)
		along with their paths.  Using these paths, we can find the values of these path parameters given by each parse tree in the intersection.
		"""

		# copy the path for the current branch
		current_path_copy = [v for v in current_path]

		for child in curr._children:
			if len(child._children) == 0 and type(child._symbol) is CFGVertex:
				# we have a leaf
				path_parameters.append(current_path_copy + [child._symbol])
			else:
				# recurse
				self.get_parameter_paths(child, current_path_copy + [child._symbol], path_parameters)

	def get_parameter_subtree(self, parameter_path):
		"""
		Given a parameter path, traverse the parse tree along that path and return a new parse tree starting
		from that root vertex.
		"""
		current_vertex = self._root_vertex
		for el in parameter_path:
			match_found = False
			for child in current_vertex._children:
				if child._symbol == el:
					current_vertex = child
					match_found = True
			if not(match_found):
				# can't follow the path through the SCFG
				return False

		# use the root vertex to construct a new parse tree
		new_parse_tree = ParseTree(empty=True, starting_vertex=current_vertex._symbol)
		self.new_parse_tree_rooted_at_vertex(new_parse_tree, current_vertex, new_parse_tree._root_vertex)

		return new_parse_tree

	def new_parse_tree_rooted_at_vertex(self, new_parse_tree, current_old_vertex, current_new_vertex):
		"""
		Recursively construct the subtree from the given root vertex.
		"""
		for child in current_old_vertex._children:
			new_child = ParseTreeVertex(child._symbol)
			new_parse_tree._vertices.append(new_child)
			current_new_vertex.add_child(new_child)
			self.new_parse_tree_rooted_at_vertex(new_parse_tree, child, new_child)