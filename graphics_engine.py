########################################################################################################################
#
#   Ryan Walters
#   Louisiana Tech University
#   2/11/17
#
#   Assignment 4:
#   This program draws three dimensional objects and manipulates them,
#   projecting results into a 2d plane so that it is viewable on a screen. It shades them using a lighting model that
#   includes faceted, gouraud, and phong shading with ambient diffuse, point diffuse, and specular highlights.
#
#   Currently can scale, rotate, and translate objects. All of which
#   can be done at different magnitudes.
#
#   It can have multiple objects on screen, with multiple objects being able to be selected at once.
#   It can perform manipulations both in place and from origin by toggling the use of world-space coordinates.
#   User can create, delete, manipulate and select any number of objects.
#   There are currently pyramids and cubes implemented.
#
#   You can toggle culling of backfaces, as well as the filling in of polygons. Polygons are filled in pixel by pixel
#   and can occlude background objects by using a z buffer
#
#
########################################################################################################################

"""
UI Guide:

*** FEEL FREE TO MAXIMIZE THE WINDOW. THIS PROGRAM FULLY SUPPORTS WINDOW SCALING.

In the center of the screen is the viewport. Meshes created are displayed here. Selected meshes are highlighted in red.
All actions you perform on an mesh are performed on all selected meshes.

The white box on the left lists all of the meshes in the world using a friendly name. you can click on the names of
meshes to select them and can drag+click, control+click, or shift+click to select multiple meshes at once. Above this
box are buttons to create and delete meshes.

At the bottom of the screen is the manipulation toolbar:
    *** ALL OF THESE BUTTONS CAN BE HELD DOWN TO GO FASTER

    * The "Reset" button resets meshes to original scale, position, and rotation
    * The "Use World-Space Coordinates" checkbox disables local rotations for the meshes

    * Use the "Scale" button to scale meshes by the multiplier shown to the left of it.
    * You can increase and decrease this multiplier using the arrow buttons.
    ** Clicking on the current multiplier text between the arrow buttons will reset the multiplier to default

    * Use the "Translation" buttons to translate meshes in the button's direction by the number of units to the left.
    * You can increase and decrease the number of units translated each click by using the arrow buttons.
    ** Clicking on the current unit size text between the arrow buttons will reset the number of units to default

    * Use the "Rotation" buttons to rotate meshes in the button's axis rotation vector by the degrees to the left.
    * You can increase and decrease the number of degrees rotated each click by using the arrow buttons.
    ** Clicking on the current number of degrees between the arrow buttons will reset the degrees to default.
"""

import math
from copy import deepcopy
from tkinter import *

CanvasWidth = 400
CanvasHeight = 400
d = 500
zbuffer = [[0 for x in range(CanvasHeight)] for y in range(CanvasWidth)]

# these are added so that we can transform by varying amounts
RotationStepSize = 5
TranslationStepSize = 5
ScaleStepSize = 1.00

# keep track of our meshes
selectedMeshes = []
allMeshes = []
meshNames = []
numMeshesCreated = 0

# stands for Not In-Place. If true, we use world-coordinate system for transformations rather than local
NIP = False

isWireframe = False  # toggle for backface culling
willNotDraw = 1313131313
isFilled = False  # toggle for filling the poly
isZbuffered = True  # toggle for Z-buffering
drawEdges = True  # toggle for drawing edges at all

lightingmode = 2  # 0 = unlit (ambient), 1 = point + ambient, 2 = point, ambient and specular
shadingmode = 2  # 0 = faceted, 1 = gouraud, 2 = phong [only used if usesSmoothing is True, else functions as 0 always]
Ip = [1,1,1]  # intensity of our point light
Ia = [1, 1, 1]  # ambient intensity in the scene


# **************************************************************************
# Our mesh object class. All meshes that we create are defined by this class. This class contains the variables and
# functions that define translations and drawings of the meshes in the engine
class Mesh:
    # These are the basic matrices  that are used for transformations. Only the indexes with a '2' need to be altered.
    translationMatrix = [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [2, 2, 2, 1]]
    scalingMatrix = [[2, 0, 0, 0], [0, 2, 0, 0], [0, 0, 2, 0], [0, 0, 0, 1]]

    xRotMatrix = [[1, 0, 0, 0], [0, 2, 2, 0], [0, 2, 2, 0], [0, 0, 0, 1]]
    yRotMatrix = [[2, 0, 2, 0], [0, 1, 0, 0], [2, 0, 2, 0], [0, 0, 0, 1]]
    zRotMatrix = [[2, 2, 0, 0], [2, 2, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]]

    meshColor = '#9999%02x'

    # Need an initializer for variables. If variables are defined above this line (like our matrices), altering them in
    # one instantiated object alters them for every instantiated object. Not what we want
    def __init__(self):
        self.polyList = []  # List of polygon faces defined in counter clockwise order when viewed from the outside
        self.pointList = []  # Definition of the underlying points
        self.pointCloud = []  # Definition of the Pyramid's underlying point cloud.  No structure, just the points.
        self.rPointCloud = []  # A copy of our input data for resetting later
        self.meshDef = []  # Definition of the object

        self.midpoint = [0, 0, 0, 1]  # location of the mesh's pivot
        # use these for determining the bounds of the object. Useful for finding midpoint
        self.smallest = [0, 0, 0, 1]  # stores the most negative of all the points' values
        self.largest = [0, 0, 0, 1]  # stores the most negative of all the points' values
        self.usesSmoothing = False

        self.Kd = [0.9, 0.2, 0.3]  # diffuse reflectivity of object
        self.Ks = 0.5  # specular reflectivity of object
        self.Kn = 16  # shininess of object

        # these are somewhat redundant as we are storing the vertex normals in the same array as the vertex coords
        self.normals = [[0.0, 0.0, 0.0]]
        self.vertexNormals = [[0.0, 0.0, 0.0]]


    # make a backup of the locations of the points so we can easily reset the mesh's position
    def initPointCloud(self):
        self.rPointCloud = deepcopy(self.pointCloud)

    # called upon object creation. Determine starting midpoint.
    def findMidpoint(self):
        for i in self.pointCloud:  # for every point,
            for j in range(0,3):  # for every dimension in the point vector
                if i[j] < self.smallest[j]:  # keep track of the smallest number in each dimension
                    self.smallest[j] = i[j]
                if i[j] > self.largest[j]:  # keep track of the largest number in each dimension
                    self.largest[j] = i[j]

        # using the smallest and largest numbers in each dimension, calculate the midpoint by taking the averages
        for i in range(len(self.midpoint)):
            self.midpoint[i] = ((self.largest[i] + self.smallest[i]) / 2)

    # keep an updated list of the surface normals and vertex normals
    def calculateNormals(self):
        self.normals = [[0.0, 0.0, 0.0]]
        self.vertexNormals = [[0.0, 0.0, 0.0]]
        for i in range(len(self.polyList)):
            self.normals.append([0.0, 0.0, 0.0])
        for i in range(len(self.pointList)):
            self.vertexNormals.append([0.0, 0.0, 0.0])

        i = 0
        # loop through and calculate the surface normals for every poly by getting the dot product of vertices
        for p in self.polyList:
            a = [p[2][0] - p[0][0], p[2][1] - p[0][1], p[2][2] - p[0][2]]  # alpha
            b = [p[1][0] - p[0][0], p[1][1] - p[0][1], p[1][2] - p[0][2]]  # beta
            self.normals[i] = [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]  # normal from product
            i += 1

        # normalize all of the surface normals by dividing each value by the magnitude of the vector
        # which is found by square rooting the sum of squares
        for i in range(len(self.normals)):
            magnitude = math.sqrt(math.pow(self.normals[i][0], 2) + math.pow(self.normals[i][1], 2) + math.pow(self.normals[i][2], 2))
            if magnitude != 0:
                self.normals[i][0] /= magnitude
                self.normals[i][1] /= magnitude
                self.normals[i][2] /= magnitude

        # for every vertex, for every poly, if vertex belongs to poly, add its value to the surface normal
        # then normalize this new vector to find the vertex normal
        h = 0
        for vertex in self.pointList:
            summ = [0.0, 0.0, 0.0]
            for j in range(len(self.polyList)):
                for i in range(0,3):
                    if self.polyList[j][i] == vertex:
                        summ[0] += self.normals[j][0]
                        summ[1] += self.normals[j][1]
                        summ[2] += self.normals[j][2]
            magnitude = math.sqrt(math.pow(summ[0], 2) + math.pow(summ[1], 2) + math.pow(summ[2], 2))
            self.vertexNormals[h][0] = summ[0] / magnitude
            self.vertexNormals[h][1] = summ[1] / magnitude
            self.vertexNormals[h][2] = summ[2] / magnitude
            # less messy to store the vertex normals alongside the vertex coordinates
            vertex[4] = self.vertexNormals[h][0]
            vertex[5] = self.vertexNormals[h][1]
            vertex[6] = self.vertexNormals[h][2]
            h += 1

    # Resets the pyramid to its original size and location in 3D space
    # by copying the value of each element from our backup to our point cloud
    def resetMesh(self):
        for i in range(len(self.pointCloud)):  # for point in our cloud
            for j in range(len(self.pointCloud[i])):  # for each dimension value
                self.pointCloud[i][j] = self.rPointCloud[i][j]  # reset each value from our backup
        self.midpoint = [0, 0, 0, 1]  # place our pivot at the origin

    # This function translates an object by some displacement.  The displacement is a 3D
    # vector so the amount of displacement in each dimension can vary.
    def translate(self, displacement):
        # grab a copy of the matrices needed for translation
        matrix = deepcopy(self.translationMatrix)
        answer = deepcopy(self.pointCloud)

        # make the bottom 3 values in our matrix equal to the displacement we want
        for i in range(0, 3):
            matrix[3][i] = displacement[i]

        # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to pointcloud
        # element by element because it doesn't work otherwise.
        for i in range(len(self.pointCloud)):
            answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
            for j in range(len(answer[i]) - 1):
                self.pointCloud[i][j] = answer[i][j]

        # displace the midpoint as well
        for j in range(0, 3):
            self.midpoint[j] += displacement[j]

    # This function performs a simple uniform scale of an object using the origin as the pivot. Scalefactor is scalar
    # TODO: if we ever want stretching we need scalefactor to be a vector
    def scaleNIP(self, scalefactor):
        # grab a copy of the matrices needed for scaling
        matrix = deepcopy(self.scalingMatrix)
        answer = deepcopy(self.pointCloud)

        # Make the matrix's diagonal equal to the scalefactor
        for i in range(0, 3):
            matrix[i][i] = scalefactor

        # since the scaling pivot is not the midpoint of the mesh, the midpoint maya move. Therefore, calculate how much
        # one point is displaced so we can apply the same displacement to the midpoint of the mesh
        answer[0] = vectorMatrixMult(self.pointCloud[0], matrix)
        for i in range(len(self.midpoint)):
            self.midpoint[i] = self.midpoint[i] - (self.pointCloud[0][i] - answer[0][i])

        # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to pointcloud
        # element by element because it doesn't work otherwise.
        for i in range(len(self.pointCloud)):
            answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
            for j in range(len(answer[i])):
                self.pointCloud[i][j] = answer[i][j]

    # scale mesh using the mesh's pivot as the scaling pivot. Scalefactor is a scalar
    def scale(self, scalefactor):
        global NIP
        # if we are using world-space coordinates, use the other scaling function
        if NIP:
            self.scaleNIP(scalefactor)
        else:
            # grab a copy of the matrices needed for scaling
            answer = deepcopy(self.pointCloud)
            matrix = deepcopy(self.scalingMatrix)

            # The composite matrix can be easily defined without multiplying matrices by replacing the translation
            # parts of the matrix with [pivot*(1-scalefactor)]
            for i in range(0, 3):
                matrix[3][i] = self.midpoint[i] * (1 - scalefactor)
                matrix[i][i] = scalefactor

            # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to
            # pointcloud element by element because it doesn't work otherwise.
            for i in range(len(self.pointCloud)):
                answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
                for j in range(len(answer[i])):
                    self.pointCloud[i][j] = answer[i][j]

    # this function rotates a mesh, either by transferring inputs to separate functions if using world-space coords, or
    # by performing the seven steps to calculate a composite matrix and multiplying the input vector by that. It takes
    # a scalar, degrees, and a string, axis, which tells the function which way to rotate the mesh.
    def rotateMesh(self, degrees, axis):
        global NIP
        # if using world-space coordinates, send input to other functions, one for each axis of rotation
        if NIP:
            if axis == 'x':
                self.rotateXNIP(degrees)
            elif axis == 'y':
                self.rotateYNIP(degrees)
            elif axis == 'z':
                self.rotateZNIP(degrees)
        else:
            radians = math.radians(-degrees)  # convert degrees to radians
            # grab a copy of the matrices needed for rotation
            transmatrix = deepcopy(self.translationMatrix)
            answer = deepcopy(self.pointCloud)

            # get our pivot then add the largest bounds to it to create the rotation vector. The largest bounds
            # insures that the vector's origin will be outside of the mesh
            p1 = deepcopy(self.midpoint)
            p1[2] += self.largest[2]

            # steps 1 and 7 are translations, so we will have a copy of the base translation matrix for each
            step1 = deepcopy(transmatrix)
            step7 = deepcopy(transmatrix)
            # step 1 needs to be negative displacement, as we need to translate it to the origin
            for i in range(0, 3):
                step1[3][i] = -self.midpoint[i]
                step7[3][i] = self.midpoint[i]

            # calculate our variables for math
            a = self.midpoint[0] - p1[0]  # a = x2 - x1
            b = self.midpoint[1] - p1[1]  # b = y2 - y1
            c = self.midpoint[2] - p1[2]  # c = z2 - z1
            p = math.sqrt(b ** 2 + c ** 2)  # p = sqrt(b^2 + c^2)
            l = math.sqrt(a ** 2 + b ** 2 + c ** 2)  # l = sqrt(a^2 + b^2 + c^2)


            # matrices used for steps 2 and 3
            step2 = [[1, 0, 0, 0],
                     [0, c / p, b / p, 0],
                     [0, -b / p, c / p, 0],
                     [0, 0, 0, 1]]

            step3 = [[p / l, 0, -a / l, 0],
                     [0, 1, 0, 0],
                     [a / l, 0, p / l, 0],
                     [0, 0, 0, 1]]

            # step 4 is the actual rotation we are calculating, so we use a different matrix depending on the axis of
            # rotation. The matrices only differ in position and sign of the cosines and sines. So we grab a copy of
            # the base rotation matrices for each rotation axis and set them up.
            if axis == 'z':
                radians = -radians
                step4 = deepcopy(self.zRotMatrix)
                step4[0][0] = math.cos(radians)
                step4[0][1] = math.sin(radians)
                step4[1][0] = -math.sin(radians)
                step4[1][1] = math.cos(radians)
            elif axis == 'y':
                step4 = deepcopy(self.yRotMatrix)
                step4[0][0] = math.cos(radians)
                step4[0][2] = -math.sin(radians)
                step4[2][0] = math.sin(radians)
                step4[2][2] = math.cos(radians)
            else:
                step4 = deepcopy(self.xRotMatrix)
                step4[1][1] = math.cos(radians)
                step4[1][2] = math.sin(radians)
                step4[2][1] = -math.sin(radians)
                step4[2][2] = math.cos(radians)

            # steps 5 and six are the reversal of 2 and 3
            step5 = [[p / l, 0, a / l, 0],
                     [0, 1, 0, 0],
                     [-a / l, 0, p / l, 0],
                     [0, 0, 0, 1]]

            step6 = [[1, 0, 0, 0],
                     [0, c / p, -b / p, 0],
                     [0, b / p, c / p, 0],
                     [0, 0, 0, 1]]

            # compute the composite matrix by multiplying each matrix in the order that we want to perform the steps.
            matrix = matrixMult4x4(step1, step2)
            matrix = matrixMult4x4(matrix, step3)
            matrix = matrixMult4x4(matrix, step4)
            matrix = matrixMult4x4(matrix, step5)
            matrix = matrixMult4x4(matrix, step6)
            matrix = matrixMult4x4(matrix, step7)

            # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to
            # pointcloud element by element because it doesn't work otherwise.
            for i in range(len(self.pointCloud)):
                answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
                for j in range(len(answer[i])):
                    self.pointCloud[i][j] = answer[i][j]

            # calculate the displacement of the pivot of our mesh
            self.midpoint = vectorMatrixMult(self.midpoint, matrix)

    # This function performs a rotation of an object about the Z axis (from +X to +Y)
    # by 'degrees', using the origin as the pivot.  The rotation is CCW
    # in a LHS when viewed from -Z [the location of the viewer in the standard postion]
    def rotateZNIP(self, degrees):
        radians = math.radians(-degrees)  # convert degrees to radians
        # grab a copy of the matrices needed for z rotation
        matrix = deepcopy(self.zRotMatrix)
        answer = deepcopy(self.pointCloud)

        # calculate the sines and cosines for insertion in the matrix
        matrix[0][0] = math.cos(radians)
        matrix[0][1] = math.sin(radians)
        matrix[1][0] = -math.sin(radians)
        matrix[1][1] = math.cos(radians)

        # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to
        # pointcloud element by element because it doesn't work otherwise.
        for i in range(len(self.pointCloud)):
            answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
            for j in range(len(answer[i])):
                self.pointCloud[i][j] = answer[i][j]

        # calculate the displacement of the pivot of our mesh
        self.midpoint = vectorMatrixMult(self.midpoint, matrix)

    # This function performs a rotation of an object about the Y axis (from +Z to +X)
    # by 'degrees', using the origin as the pivot.  The rotation is CW
    # in a LHS when viewed from +Y looking toward the origin.
    def rotateYNIP(self, degrees):
        radians = math.radians(degrees)  # convert degrees to radians
        # grab a copy of the matrices needed for z rotation
        matrix = deepcopy(self.yRotMatrix)
        answer = deepcopy(self.pointCloud)

        # calculate the sines and cosines for insertion in the matrix
        matrix[0][0] = math.cos(radians)
        matrix[0][2] = -math.sin(radians)
        matrix[2][0] = math.sin(radians)
        matrix[2][2] = math.cos(radians)

        # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to
        # pointcloud element by element because it doesn't work otherwise.
        for i in range(len(self.pointCloud)):
            answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
            for j in range(len(answer[i])):
                self.pointCloud[i][j] = answer[i][j]

        # calculate the displacement of the pivot of our mesh
        self.midpoint = vectorMatrixMult(self.midpoint, matrix)

    # This function performs a rotation of an object about the X axis (from +Y to +Z)
    # by 'degrees', using the origin as the pivot.  The rotation is CW
    # in a LHS when viewed from +X looking toward the origin.
    def rotateXNIP(self, degrees):
        radians = math.radians(-degrees)  # convert degrees to radians
        # grab a copy of the matrices needed for z rotation
        matrix = deepcopy(self.xRotMatrix)
        answer = deepcopy(self.pointCloud)

        # calculate the sines and cosines for insertion in the matrix
        matrix[1][1] = math.cos(radians)
        matrix[1][2] = math.sin(radians)
        matrix[2][1] = -math.sin(radians)
        matrix[2][2] = math.cos(radians)

        # do our matrix multiplication for every point in our mesh. We store it in answer then transfer it to
        # pointcloud element by element because it doesn't work otherwise.
        for i in range(len(self.pointCloud)):
            answer[i] = vectorMatrixMult(self.pointCloud[i], matrix)
            for j in range(len(answer[i])):
                self.pointCloud[i][j] = answer[i][j]

        # calculate the displacement of the pivot of our mesh
        self.midpoint = vectorMatrixMult(self.midpoint, matrix)

    # The function will draw an object by repeatedly calling drawPoly on each polygon in the object
    def drawObject(self, selected):
        self.calculateNormals()
        for poly in self.meshDef:  # for each polygon,
            self.drawPoly(poly, selected)  # send it to drawPoly()

    # This function will draw a polygon by repeatedly calling drawLine on each pair of points
    # making up the object.  Remember to draw a line between the last point and the first.
    def drawPoly(self, poly, selected):
        if not isWireframe:
            if self.checkIfBackface(poly):
                return
        if isFilled:
            self.fillPolygon(poly)
        if drawEdges:
            for i in range(len(poly)):  # for each point in the polygon (most likely only 3 but arbitrary for compatibility)
                if i == len(poly) - 1:  # if last point in polygon,
                    self.drawLine(poly[i], poly[0], selected)  # draw line from last point to first
                else:  # if not last point,
                    self.drawLine(poly[i], poly[i + 1], selected)  # draw line from current point to the next point

    # This function checks whether or not a polygon is facing away from you, and therefore needs to be culled
    def checkIfBackface(self, p):
        global d
        a = [p[2][0] - p[0][0], p[2][1] - p[0][1], p[2][2] - p[0][2]]  # alpha
        b = [p[1][0] - p[0][0], p[1][1] - p[0][1], p[1][2] - p[0][2]]  # beta

        norm = [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]  # normal from product

        # calculate the center of the polygonal face
        center = [(p[0][0] + p[1][0] + p[2][0]) / 3, (p[0][1] + p[1][1] + p[2][1]) / 3,
                  (p[0][2] + p[1][2] + p[2][2]) / 3]

        view = [center[0] - 0, center[1] - 0, center[2] - d]  # calculate the vector between the viewer and the polygon

        if (view[0] * norm[0] + view[1] * norm[1] + view[2] * norm[2]) < 0:  # vector product to check orientation
            return False
        else:
            return True

    # this function fills the polygonal faces pixel by pixel using scanlines and gradients the color
    def fillPolygon(self, poly2):
        global willNotDraw, shadingmode, d
        filltable = [[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0], [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
                     [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0]]  # edge table extended from notes
        poly = deepcopy(poly2)
        p = deepcopy(poly2)

        for i in range(len(poly)):
            poly[i] = self.convertToDisplayCoordinates(self.project(poly[i]))  # convert the polys to 2D

        # pre-calculate the vertex lighting intensities using vertex normals and the view vector
        a0 = self.light([poly[0][4], poly[0][5], poly[0][6]], [poly[0][0], poly[0][1], poly[0][2] - d])
        a1 = self.light([poly[1][4], poly[1][5], poly[1][6]], [poly[1][0], poly[1][1], poly[1][2] - d])
        a2 = self.light([poly[2][4], poly[2][5], poly[2][6]], [poly[2][0], poly[2][1], poly[2][2] - d])

        # TODO: Might need to round or distort the min and max values?
        # each edge in the edge table needs to be set up. The next two blocks are identical so I won't comment them
        filltable[0][0] = max(poly[0][1], poly[1][1])  # max Y
        filltable[0][1] = min(poly[0][1], poly[1][1])  # min Y
        if poly[1][1] == poly[0][1]:
            filltable[0][2] = 0  # if line is horizontal, then we won't draw it
        else:
            filltable[0][2] = -((poly[1][0] - poly[0][0]) / (poly[1][1] - poly[0][1]))  # calculate dX as -deltaX/deltaY
        if poly[0][1] > poly[1][1]:  # calculate the maximum X value for the line
            maxx = poly[0][0]
        else:
            maxx = poly[1][0]
        filltable[0][3] = maxx + (filltable[0][2] / 2)  # initial x value -> max X + dX/2
        filltable[0][4] = poly[0][0]  # we need a random X and Y pair from the line
        filltable[0][5] = poly[0][1]  # ""
        # calculate the Z value of the point owning the larger Y value and the dZ of that point, making sure to not
        # divide by zero by just setting the dz to 0 for a constant z value
        if poly[0][1] < poly[1][1]:  # we do these blocks based on which y-value is larger, as we work our way down
            filltable[0][6] = poly[0][2]
            # 9, 10, and 11 store either the vertex normal, or its intensity. The lerp math doesn't change regardless
            filltable[0][9] = poly[0][4]
            filltable[0][10] = poly[0][5]
            filltable[0][11] = poly[0][6]
            if shadingmode == 1:  # if gouraud, we store the intensities rather than the normals to lerp through
                filltable[0][9] = a0[0]
                filltable[0][10] = a0[1]
                filltable[0][11] = a0[2]
            if poly[0][1] == poly[1][1]:  # if y values are equal, the deltas are zero.
                filltable[0][7], filltable[0][12], filltable[0][13], filltable[0][14] = 0, 0, 0, 0
            else:
                filltable[0][7] = (poly[0][2] - poly[1][2]) / (poly[0][1] - poly[1][1])
                # 12, 13, and 14 store the delta step size for either the RGB intensities or the XYZ vertex normals
                filltable[0][12] = (poly[0][4] - poly[1][4]) / (poly[0][1] - poly[1][1])
                filltable[0][13] = (poly[0][5] - poly[1][5]) / (poly[0][1] - poly[1][1])
                filltable[0][14] = (poly[0][6] - poly[1][6]) / (poly[0][1] - poly[1][1])
                if shadingmode == 1:  # again, if gouraud, the step size deltas must be between the intensities
                    filltable[0][12] = (a0[0] - a1[0]) / (poly[0][1] - poly[1][1])
                    filltable[0][13] = (a0[1] - a1[1]) / (poly[0][1] - poly[1][1])
                    filltable[0][14] = (a0[2] - a1[2]) / (poly[0][1] - poly[1][1])
            filltable[0][8] = poly[1][2]
        else:  # this is the second block. Used if the other vertex has larger Y. Inner code is identical so uncommented
            filltable[0][6] = poly[1][2]
            filltable[0][9] = poly[1][4]
            filltable[0][10] = poly[1][5]
            filltable[0][11] = poly[1][6]
            if shadingmode == 1:
                filltable[0][9] = a1[0]
                filltable[0][10] = a1[1]
                filltable[0][11] = a1[2]
            if poly[1][1] == poly[0][1]:
                filltable[0][7], filltable[0][12], filltable[0][13], filltable[0][14] = 0, 0, 0, 0
            else:
                filltable[0][7] = (poly[1][2] - poly[0][2]) / (poly[1][1] - poly[0][1])
                filltable[0][12] = (poly[1][4] - poly[0][4]) / (poly[1][1] - poly[0][1])
                filltable[0][13] = (poly[1][5] - poly[0][5]) / (poly[1][1] - poly[0][1])
                filltable[0][14] = (poly[1][6] - poly[0][6]) / (poly[1][1] - poly[0][1])
                if shadingmode == 1:
                    filltable[0][12] = (a1[0] - a0[0]) / (poly[1][1] - poly[0][1])
                    filltable[0][13] = (a1[1] - a0[1]) / (poly[1][1] - poly[0][1])
                    filltable[0][14] = (a1[2] - a0[2]) / (poly[1][1] - poly[0][1])
            filltable[0][8] = poly[0][2]
        filltable[0][15] = 1  # each line segment needs a separate counter for looping and applying deltas

        filltable[1][0] = max(poly[1][1], poly[2][1])
        filltable[1][1] = min(poly[1][1], poly[2][1])
        if poly[2][1] == poly[1][1]:
            filltable[1][2] = 0
        else:
            filltable[1][2] = -((poly[2][0] - poly[1][0]) / (poly[2][1] - poly[1][1]))
        if poly[1][1] > poly[2][1]:
            maxx = poly[1][0]
        else:
            maxx = poly[2][0]
        filltable[1][3] = maxx + (filltable[1][2] / 2)
        filltable[1][4] = poly[1][0]
        filltable[1][5] = poly[1][1]
        if poly[1][1] < poly[2][1]:
            filltable[1][6] = poly[1][2]
            filltable[1][9] = poly[1][4]
            filltable[1][10] = poly[1][5]
            filltable[1][11] = poly[1][6]
            if shadingmode == 1:
                filltable[1][9] = a1[0]
                filltable[1][10] = a1[1]
                filltable[1][11] = a1[2]
            if poly[1][1] == poly[2][1]:
                filltable[1][7], filltable[1][12], filltable[1][13], filltable[1][14] = 0, 0, 0, 0
            else:
                filltable[1][7] = (poly[1][2] - poly[2][2]) / (poly[1][1] - poly[2][1])
                filltable[1][12] = (poly[1][4] - poly[2][4]) / (poly[1][1] - poly[2][1])
                filltable[1][13] = (poly[1][5] - poly[2][5]) / (poly[1][1] - poly[2][1])
                filltable[1][14] = (poly[1][6] - poly[2][6]) / (poly[1][1] - poly[2][1])
                if shadingmode == 1:
                    filltable[1][12] = (a1[0] - a2[0]) / (poly[1][1] - poly[2][1])
                    filltable[1][13] = (a1[1] - a2[1]) / (poly[1][1] - poly[2][1])
                    filltable[1][14] = (a1[2] - a2[2]) / (poly[1][1] - poly[2][1])
            filltable[1][8] = poly[2][2]
        else:
            filltable[1][6] = poly[2][2]
            filltable[1][9] = poly[2][4]
            filltable[1][10] = poly[2][5]
            filltable[1][11] = poly[2][6]
            if shadingmode == 1:
                filltable[1][9] = a2[0]
                filltable[1][10] = a2[1]
                filltable[1][11] = a2[2]
            if poly[1][1] == poly[2][1]:
                filltable[1][7], filltable[1][12], filltable[1][13], filltable[1][14] = 0, 0, 0, 0
            else:
                filltable[1][7] = (poly[2][2] - poly[1][2]) / (poly[2][1] - poly[1][1])
                filltable[1][12] = (poly[2][4] - poly[1][4]) / (poly[2][1] - poly[1][1])
                filltable[1][13] = (poly[2][5] - poly[1][5]) / (poly[2][1] - poly[1][1])
                filltable[1][14] = (poly[2][6] - poly[1][6]) / (poly[2][1] - poly[1][1])
                if shadingmode == 1:
                    filltable[1][12] = (a2[0] - a1[0]) / (poly[2][1] - poly[1][1])
                    filltable[1][13] = (a2[1] - a1[1]) / (poly[2][1] - poly[1][1])
                    filltable[1][14] = (a2[2] - a1[2]) / (poly[2][1] - poly[1][1])
            filltable[1][8] = poly[1][2]
        filltable[1][15] = 1

        filltable[2][0] = max(poly[0][1], poly[2][1])
        filltable[2][1] = min(poly[0][1], poly[2][1])
        if poly[2][1] == poly[0][1]:
            filltable[2][2] = 0
        else:
            filltable[2][2] = -((poly[2][0] - poly[0][0]) / (poly[2][1] - poly[0][1]))
        if poly[0][1] > poly[2][1]:
            maxx = poly[0][0]
        else:
            maxx = poly[2][0]
        filltable[2][3] = maxx + (filltable[2][2] / 2)
        filltable[2][4] = poly[2][0]
        filltable[2][5] = poly[2][1]
        if poly[0][1] < poly[2][1]:
            filltable[2][6] = poly[0][2]
            filltable[2][9] = poly[0][4]
            filltable[2][10] = poly[0][5]
            filltable[2][11] = poly[0][6]
            if shadingmode == 1:
                filltable[2][9] = a0[0]
                filltable[2][10] = a0[1]
                filltable[2][11] = a0[2]
            if poly[0][1] == poly[2][1]:
                filltable[2][7], filltable[2][12], filltable[2][13], filltable[2][14] = 0, 0, 0, 0
            else:
                filltable[2][7] = (poly[0][2] - poly[2][2]) / (poly[0][1] - poly[2][1])
                filltable[2][12] = (poly[0][4] - poly[2][4]) / (poly[0][1] - poly[2][1])
                filltable[2][13] = (poly[0][5] - poly[2][5]) / (poly[0][1] - poly[2][1])
                filltable[2][14] = (poly[0][6] - poly[2][6]) / (poly[0][1] - poly[2][1])
                if shadingmode == 1:
                    filltable[2][12] = (a0[0] - a2[0]) / (poly[0][1] - poly[2][1])
                    filltable[2][13] = (a0[1] - a2[1]) / (poly[0][1] - poly[2][1])
                    filltable[2][14] = (a0[2] - a2[2]) / (poly[0][1] - poly[2][1])
            filltable[2][8] = poly[2][2]
        else:
            filltable[2][6] = poly[2][2]
            filltable[2][9] = poly[2][4]
            filltable[2][10] = poly[2][5]
            filltable[2][11] = poly[2][6]
            if shadingmode == 1:
                filltable[2][9] = a2[0]
                filltable[2][10] = a2[1]
                filltable[2][11] = a2[2]
            if poly[0][1] == poly[2][1]:
                filltable[2][7], filltable[2][12], filltable[2][13], filltable[2][14] = 0, 0, 0, 0
            else:
                filltable[2][7] = (poly[2][2] - poly[0][2]) / (poly[2][1] - poly[0][1])
                filltable[2][12] = (poly[2][4] - poly[0][4]) / (poly[2][1] - poly[0][1])
                filltable[2][13] = (poly[2][5] - poly[0][5]) / (poly[2][1] - poly[0][1])
                filltable[2][14] = (poly[2][6] - poly[0][6]) / (poly[2][1] - poly[0][1])
                if shadingmode == 1:
                    filltable[2][12] = (a2[0] - a0[0]) / (poly[2][1] - poly[0][1])
                    filltable[2][13] = (a2[1] - a0[1]) / (poly[2][1] - poly[0][1])
                    filltable[2][14] = (a2[2] - a0[2]) / (poly[2][1] - poly[0][1])
            filltable[2][8] = poly[0][2]
        filltable[2][15] = 1

        yMax = max(filltable[0][0], filltable[1][0])  # maximum Y value for the entire poly
        yMin = min(filltable[0][1], filltable[1][1])  # minimum Y value for the entire poly
        yMidl = sorted([poly[0][1], poly[1][1], poly[2][1]])
        yMid = yMidl[1]

        currline = yMin + 1  # where to start our scanlines
        loopcounter = 0  # needed for counting the RELATIVE position, rather than the screen position

        a = [p[2][0] - p[0][0], p[2][1] - p[0][1], p[2][2] - p[0][2]]  # alpha
        b = [p[1][0] - p[0][0], p[1][1] - p[0][1], p[1][2] - p[0][2]]  # beta
        norm = [a[1] * b[2] - a[2] * b[1], a[2] * b[0] - a[0] * b[2], a[0] * b[1] - a[1] * b[0]]  # normal from product
        # calculate the center of the polygonal face
        center = [(p[0][0] + p[1][0] + p[2][0]) / 3, (p[0][1] + p[1][1] + p[2][1]) / 3,
                  (p[0][2] + p[1][2] + p[2][2]) / 3]
        view = [(center[0] - 0), (center[1] - 0), (center[2] - d)]  # calculate the vector between the viewer and the polygon
        lighting = self.light(norm, view)
        pixelColor = '#%02x%02x%02x' % (int(clamp(lighting[0]*255)), int(clamp(lighting[1]*255)), int(clamp(lighting[2]*255)))

        # PIXEL PAINTING
        # The following block handles the actual drawing as well as z-buffering, pixel by pixel
        while currline < yMax:  # while we are between the min and max Y values of the polygon
            loopcounter += 1
            if currline == int(yMid):
                loopcounter = 1
            xcoords = []
            zcoords = []
            shadingvalueX = []
            shadingvalueY = []
            shadingvalueZ = []
            for line in filltable:
                if line[2] != willNotDraw:
                    if line[0] > currline > line[1]:  # if we are between the min and max values for the line
                        xcoords.append(line[4] - (line[2] * (currline - line[5])))  # add an X coordinate to our list
                        zcoords.append(line[6] + (line[15] * line[7]))  # as well as the corresponding z coordinate
                        # find the lerp values for shading
                        shadingvalueX.append(line[9] + (line[15] * line[12]))
                        shadingvalueY.append(line[10] + (line[15] * line[13]))
                        shadingvalueZ.append(line[11] + (line[15] * line[14]))
                        # use each line's loop counter separately
                        line[15] += 1

            # if we only hit one point or a horizontal line, next loop
            if len(xcoords) < 2:
                currline += 1
                continue

            # sanity check
            if len(xcoords) > 2:
                print("WTF")

            # sort our point lists from smallest to largest
            if xcoords[1] < xcoords[0]:
                temp = xcoords[0]
                xcoords[0] = xcoords[1]
                xcoords[1] = temp
                temp = zcoords[0]
                zcoords[0] = zcoords[1]
                zcoords[1] = temp
                temp = shadingvalueX[0]
                shadingvalueX[0] = shadingvalueX[1]
                shadingvalueX[1] = temp
                temp = shadingvalueY[0]
                shadingvalueY[0] = shadingvalueY[1]
                shadingvalueY[1] = temp
                temp = shadingvalueZ[0]
                shadingvalueZ[0] = shadingvalueZ[1]
                shadingvalueZ[1] = temp

            currPixel = xcoords[0]  # starting point
            global zbuffer

            innerloopcounter = 0  # needed for RELATIVE position

            # until we hit the rightmost x coordinate
            while currPixel < xcoords[1]:
                # the following block clamps the values in the canvas area so we don't get out of bounds errors
                buffcurrline = currline
                buffcurrPixel = currPixel
                if currPixel < 0:
                    buffcurrPixel = 0
                if currPixel > CanvasWidth - 1:
                    buffcurrPixel = CanvasWidth - 1
                if currline < 0:
                    buffcurrline = 0
                if currline > CanvasHeight - 1:
                    buffcurrline = CanvasHeight - 1

                dz = (zcoords[1] - zcoords[0]) / (xcoords[1] - xcoords[0])  # precalculate our deltas for z
                # calculate second lerp's delta step size for shading
                dsX = (shadingvalueX[1] - shadingvalueX[0]) / (xcoords[1] - xcoords[0])
                dsY = (shadingvalueY[1] - shadingvalueY[0]) / (xcoords[1] - xcoords[0])
                dsZ = (shadingvalueZ[1] - shadingvalueZ[0]) / (xcoords[1] - xcoords[0])

                # if the curr zbuffer value is less than what we are entering, continue
                if zbuffer[int(buffcurrPixel)][int(buffcurrline)] < zcoords[0] + innerloopcounter * dz or isZbuffered is False:
                    if innerloopcounter == 0:
                        zbuffer[int(buffcurrPixel)][int(buffcurrline)] = zcoords[0]
                    else:
                        # set our z value in the buffer equal to the linearly interpolated z value from the points
                        # (z = starting z + step number * step size)
                        zbuffer[int(buffcurrPixel)][int(buffcurrline)] = zcoords[0] + innerloopcounter * dz
                    # do the same for our shading values
                    Ix = shadingvalueX[0] + innerloopcounter * dsX
                    Iy = shadingvalueY[0] + innerloopcounter * dsY
                    Iz = shadingvalueZ[0] + innerloopcounter * dsZ

                    # find the vector from the current pixel to the camera
                    view = [currPixel, currline, (zbuffer[int(buffcurrPixel)][int(buffcurrline)] - d)]
                    # differentiate what we are lerping based on whether gouraud or phong
                    if shadingmode == 2 and self.usesSmoothing:
                        lighting = self.light([Ix,Iy,Iz], view)
                    elif shadingmode == 1 and self.usesSmoothing:
                        lighting = [Ix, Iy, Iz]

                    # apply our lighting model to each pixel
                    pixelColor = '#%02x%02x%02x' % (int(clamp(lighting[0] * 255)), int(clamp(lighting[1] * 255)), int(clamp(lighting[2] * 255)))
                    # I tried several "pixel" drawing methods and chose what I felt was the fastest
                    w.create_rectangle(currPixel-1, currline-1, currPixel + 1, currline+1, width=0, fill=pixelColor)
                innerloopcounter += 1
                currPixel += 1

            currline += 1

    def light(self, norm, view):
        global Ia, Ip, lightingmode, shadingmode
        Kd = self.Kd
        Ks = self.Ks
        Kn = self.Kn
        light = [-0.5, 1.0, 1.0]
        d = 1

        I = [0.0, 0.0, 0.0]

        a = math.sqrt(math.pow(norm[0], 2) + math.pow(norm[1], 2) + math.pow(norm[2], 2))
        n = [norm[0] / a, norm[1] / a, norm[2] / a]
        a = math.sqrt(math.pow(view[0], 2) + math.pow(view[1], 2) + math.pow(view[2], 2))
        v = [view[0] / a, view[1] / a, view[2] / a]
        a = math.sqrt(math.pow(light[0], 2) + math.pow(light[1], 2) + math.pow(light[2], 2))
        l = [light[0] / a, light[1] / a, light[2] / a]

        ndotl = n[0]*l[0] + n[1]*l[1] + n[2]*l[2]
        rdotv = 1
        if lightingmode == 2 and shadingmode == 2 and self.usesSmoothing:
            r = self.getR(n, l)
            rdotv = r[0] * v[0] + r[1] * v[1] + r[2] * v[2]

        for i in range(len(I)):
            I[i] = Ia[i] * Kd[i]
            if lightingmode != 0:
                I[i] += Ip[i] * Kd[i] * ndotl / d
                if lightingmode == 2 and shadingmode == 2 and self.usesSmoothing:
                    I[i] += Ip[i] * Ks * math.pow(rdotv, Kn)

        return I

    def getR(self, n, l):
        tcphi = 2*(n[0]*l[0]+n[1]*l[1]+n[2]*l[2])  # 2 cos phi
        if tcphi > 0:
            r = [n[0]-l[0]/tcphi, n[1]-l[1]/tcphi, n[2]-l[2]/tcphi]
        elif tcphi == 0:
            r = [-l[0], -l[1], -l[2]]
        else:
            r = [-n[0]+l[0]/tcphi, -n[1]+l[1]/tcphi, -n[2]+l[2]/tcphi]
        a = math.sqrt(r[0]**2 + r[1]**2 + r[2]**2)
        return [r[0]/a, r[1]/a, r[2]/a]

    # Project the 3D endpoints to 2D point using a perspective projection implemented in 'project'
    # Convert the projected endpoints to display coordinates via a call to 'convertToDisplayCoordinates'
    # draw the actual line using the built-in create_line method. 'selected' is a boolean for determining object color
    def drawLine(self, start, end, selected):
        # send the starting and ending point coords to the project method, then convert them to display
        # #coords to store to local var
        startdisplay = self.convertToDisplayCoordinates(self.project(start))
        enddisplay = self.convertToDisplayCoordinates(self.project(end))
        # use TKinter's create line method using our two points. If object is selected, make line red.
        if selected:
            w.create_line(startdisplay[0], startdisplay[1], enddisplay[0], enddisplay[1], fill="red")
        else:
            w.create_line(startdisplay[0], startdisplay[1], enddisplay[0], enddisplay[1])

    # This function converts from 3D to 2D (+ depth) using the perspective projection technique.  Note that it
    # will return a NEW list of points.  We will not want to keep around the projected points in our object as
    # they are only used in rendering
    def project(self, point):
        # create new list to return projected points without altering our shape definition
        # TODO: I CHANGED THE FINAL D FROM -D
        ps = [(d * point[0]) / (-d + point[2]), (d * point[1]) / (-d + point[2]), point[2], point[3], point[4], point[5], point[6]]
        # ps = [(d * point[0]) / (-d + point[2]), (d * point[1]) / (-d + point[2]), point[2] / (-d + point[2])]
        return ps

    # This function converts a 2D point to display coordinates in the tk system.  Note that it will return a
    # NEW list of points.  We will not want to keep around the display coordinate points in our object as
    # they are only used in rendering.
    def convertToDisplayCoordinates(self, point):
        # create new list to return converted points without altering our shape definition
        displayXY = [0.5 * CanvasWidth + point[0], 0.5 * CanvasHeight + point[1], point[2], point[3], point[4], point[5], point[6]]
        return displayXY


# *******************************
# Object Manipulation Functions #
# *******************************

# Each of these functions just serves to call the internal manipulation functions on an object, but they loop through
# all selected objects and perform the manipulations on all of them

def drawScreen():
    global allMeshes
    global selectedMeshes
    global zbuffer

    zbuffer = [[-9999999999 for x in range(CanvasHeight)] for y in range(CanvasWidth)]

    w.delete(ALL)
    for i in allMeshes:
        i.drawObject(False)

    for i in selectedMeshes:
        i.drawObject(True)


# ***************************


def reset():
    global selectedMeshes
    for i in selectedMeshes:
        i.resetMesh()
    drawScreen()


def scaler():
    global selectedMeshes
    for i in selectedMeshes:
        i.scale(ScaleStepSize)
    drawScreen()


def larger():
    global selectedMeshes
    for i in selectedMeshes:
        i.scale(1 + ScaleStepSize)
    drawScreen()


def smaller():
    global selectedMeshes
    for i in selectedMeshes:
        i.scale(1 - ScaleStepSize)
    drawScreen()


def forward():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([0, 0, -TranslationStepSize, 1])
    drawScreen()


def backward():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([0, 0, TranslationStepSize, 1])
    drawScreen()


def left():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([TranslationStepSize, 0, 0, 1])
    drawScreen()


def right():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([-TranslationStepSize, 0, 0, 1])
    drawScreen()


def up():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([0, TranslationStepSize, 0, 1])
    drawScreen()


def down():
    global selectedMeshes
    for i in selectedMeshes:
        i.translate([0, -TranslationStepSize, 0, 1])
    drawScreen()


def xPlus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(RotationStepSize, 'x')
    drawScreen()


def xMinus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(-RotationStepSize, 'x')
    drawScreen()


def yPlus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(RotationStepSize, 'y')
    drawScreen()


def yMinus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(-RotationStepSize, 'y')
    drawScreen()


def zPlus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(RotationStepSize, 'z')
    drawScreen()


def zMinus():
    global selectedMeshes
    for i in selectedMeshes:
        i.rotateMesh(-RotationStepSize, 'z')
    drawScreen()


# *******************************************************
# ******************* Other Functions *******************

# create a mesh and define it as a pyramid
def makePyramid():
    pyramidMesh = Mesh()
    global selectedMeshes
    global allMeshes
    global numMeshesCreated

    pyramidMesh.meshColor = '#0000%02x'

    pyramidMesh.Kd =[0.1, 0.1, 0.9]

    # Definition of the underlying points
    pyramidMesh.pointList.append([0, 50, 0, 1, 0, 0, 0])
    pyramidMesh.pointList.append([-50, -50, -50, 1, 0, 0, 0])
    pyramidMesh.pointList.append([50, -50, -50, 1, 0, 0, 0])
    pyramidMesh.pointList.append([50, -50, 50, 1, 0, 0, 0])
    pyramidMesh.pointList.append([-50, -50, 50, 1, 0, 0, 0])

    # Definition of the polygons
    # Polys are defined in counter clockwise order when viewed from the outside
    pyramidMesh.polyList.append([pyramidMesh.pointList[0], pyramidMesh.pointList[1], pyramidMesh.pointList[2]])
    pyramidMesh.polyList.append([pyramidMesh.pointList[0], pyramidMesh.pointList[2], pyramidMesh.pointList[3]])
    pyramidMesh.polyList.append([pyramidMesh.pointList[0], pyramidMesh.pointList[3], pyramidMesh.pointList[4]])
    pyramidMesh.polyList.append([pyramidMesh.pointList[0], pyramidMesh.pointList[4], pyramidMesh.pointList[1]])
    pyramidMesh.polyList.append([pyramidMesh.pointList[4], pyramidMesh.pointList[3], pyramidMesh.pointList[2]])
    pyramidMesh.polyList.append([pyramidMesh.pointList[1], pyramidMesh.pointList[4], pyramidMesh.pointList[2]])

    # Definition of the object
    pyramidMesh.meshDef = [pyramidMesh.polyList[0], pyramidMesh.polyList[1], pyramidMesh.polyList[2],
                           pyramidMesh.polyList[3], pyramidMesh.polyList[4], pyramidMesh.polyList[5]]

    # Definition of the Pyramid's underlying point cloud.  No structure, just the points.
    for i in pyramidMesh.pointList:
        pyramidMesh.pointCloud.append(i)

    # initialize point cloud copy for resetting
    pyramidMesh.initPointCloud()

    # add new mesh to our selected meshes and our list of all meshes
    selectedMeshes = [pyramidMesh]
    allMeshes.append(pyramidMesh)

    meshNames.append(["pyramid" + str(numMeshesCreated)])  # add a user-friendly name to be associated with the mesh
    numMeshesCreated += 1  # increment the counter for meshes
    updateMeshList()  # update our UI's mesh list
    pyramidMesh.findMidpoint()  # find the midpoint of our new object
    drawScreen()  # draw the screen
    updateTitleBar()
    return pyramidMesh


# create a mesh and define it as a cube
def makeCube():
    cubeMesh = Mesh()
    global selectedMeshes
    global allMeshes
    global numMeshesCreated

    # for num in range(0,5):
    # Definition of the underlying points
    cubeMesh.pointList.append([-50, 50, -50, 1, 0, 0, 0])  # 0
    cubeMesh.pointList.append([50, 50, -50, 1, 0, 0, 0])  # 1
    cubeMesh.pointList.append([50, 50, 50, 1, 0, 0, 0])  # 2
    cubeMesh.pointList.append([-50, 50, 50, 1, 0, 0, 0])  # 3
    cubeMesh.pointList.append([-50, -50, -50, 1, 0, 0, 0])  # 4
    cubeMesh.pointList.append([50, -50, -50, 1, 0, 0, 0])  # 5
    cubeMesh.pointList.append([50, -50, 50, 1, 0, 0, 0])  # 6
    cubeMesh.pointList.append([-50, -50, 50, 1, 0, 0, 0])  # 7

    # Definition of the polygons
    # Polys are defined in counter clockwise order when viewed from the outside
    cubeMesh.polyList.append([cubeMesh.pointList[0], cubeMesh.pointList[1], cubeMesh.pointList[3]])
    cubeMesh.polyList.append([cubeMesh.pointList[1], cubeMesh.pointList[2], cubeMesh.pointList[3]])
    cubeMesh.polyList.append([cubeMesh.pointList[1], cubeMesh.pointList[0], cubeMesh.pointList[5]])
    cubeMesh.polyList.append([cubeMesh.pointList[0], cubeMesh.pointList[4], cubeMesh.pointList[5]])
    cubeMesh.polyList.append([cubeMesh.pointList[1], cubeMesh.pointList[5], cubeMesh.pointList[2]])
    cubeMesh.polyList.append([cubeMesh.pointList[2], cubeMesh.pointList[5], cubeMesh.pointList[6]])
    cubeMesh.polyList.append([cubeMesh.pointList[2], cubeMesh.pointList[6], cubeMesh.pointList[7]])
    cubeMesh.polyList.append([cubeMesh.pointList[2], cubeMesh.pointList[7], cubeMesh.pointList[3]])
    cubeMesh.polyList.append([cubeMesh.pointList[3], cubeMesh.pointList[7], cubeMesh.pointList[4]])
    cubeMesh.polyList.append([cubeMesh.pointList[4], cubeMesh.pointList[0], cubeMesh.pointList[3]])
    cubeMesh.polyList.append([cubeMesh.pointList[4], cubeMesh.pointList[7], cubeMesh.pointList[5]])
    cubeMesh.polyList.append([cubeMesh.pointList[5], cubeMesh.pointList[7], cubeMesh.pointList[6]])

    # Definition of the object
    cubeMesh.meshDef = [cubeMesh.polyList[0], cubeMesh.polyList[1], cubeMesh.polyList[2], cubeMesh.polyList[3],
                        cubeMesh.polyList[4], cubeMesh.polyList[5], cubeMesh.polyList[6], cubeMesh.polyList[7],
                        cubeMesh.polyList[8], cubeMesh.polyList[9], cubeMesh.polyList[10], cubeMesh.polyList[11]]

    # Definition of the Pyramid's underlying point cloud.  No structure, just the points.
    for i in cubeMesh.pointList:
        cubeMesh.pointCloud.append(i)

        # initialize point cloud copy for resetting
        cubeMesh.initPointCloud()

    # add new mesh to our selected meshes and our list of all meshes
    selectedMeshes = [cubeMesh]
    allMeshes.append(cubeMesh)

    meshNames.append(["cube" + str(numMeshesCreated)])  # add a user-friendly name to be associated with the mesh
    numMeshesCreated += 1  # increment the counter for meshes
    updateMeshList()  # update our UI's mesh list
    cubeMesh.findMidpoint()  # find the midpoint of our new object
    drawScreen()  # draw the screen
    updateTitleBar()
    return cubeMesh


# create a mesh and define it as a pyramid
def makeCap():
    capMesh = Mesh()
    global selectedMeshes
    global allMeshes
    global numMeshesCreated

    capMesh.meshColor = '#0000%02x'

    # Definition of the underlying points
    capMesh.pointList.append([0, 0, 0, 1, 0, 0, 0])
    capMesh.pointList.append([0, 0, 100, 1, 0, 0, 0])
    capMesh.pointList.append([70.710678, 0, 70.710678, 1, 0, 0, 0])
    capMesh.pointList.append([100, 0, 0, 1, 0, 0, 0])
    capMesh.pointList.append([70.710678, 0, -70.710678, 1, 0, 0, 0])
    capMesh.pointList.append([0, 0, -100, 1, 0, 0, 0])
    capMesh.pointList.append([-70.710678, 0, -70.710678, 1, 0, 0, 0])
    capMesh.pointList.append([-100, 0, 0, 1, 0, 0, 0])
    capMesh.pointList.append([-70.710678, 0, 70.710678, 1, 0, 0, 0])


    # Definition of the polygons
    # Polys are defined in counter clockwise order when viewed from the outside
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[2], capMesh.pointList[1]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[3], capMesh.pointList[2]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[4], capMesh.pointList[3]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[5], capMesh.pointList[4]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[6], capMesh.pointList[5]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[7], capMesh.pointList[6]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[8], capMesh.pointList[7]])
    capMesh.polyList.append([capMesh.pointList[0], capMesh.pointList[1], capMesh.pointList[8]])

    # Definition of the object
    capMesh.meshDef = [capMesh.polyList[0], capMesh.polyList[1], capMesh.polyList[2], capMesh.polyList[3],
                       capMesh.polyList[4], capMesh.polyList[5], capMesh.polyList[6], capMesh.polyList[7]]

    # Definition of the Pyramid's underlying point cloud.  No structure, just the points.
    for i in capMesh.pointList:
        capMesh.pointCloud.append(i)

    # initialize point cloud copy for resetting
        capMesh.initPointCloud()

    # add new mesh to our selected meshes and our list of all meshes
    selectedMeshes = [capMesh]
    allMeshes.append(capMesh)

    meshNames.append(["cap" + str(numMeshesCreated)])  # add a user-friendly name to be associated with the mesh
    numMeshesCreated += 1  # increment the counter for meshes
    updateMeshList()  # update our UI's mesh list
    capMesh.findMidpoint()  # find the midpoint of our new object
    drawScreen()  # draw the screen
    updateTitleBar()
    return capMesh


# create a mesh and define it as a pyramid
def makeTube():
    tubeMesh = Mesh()
    global selectedMeshes
    global allMeshes
    global numMeshesCreated

    tubeMesh.meshColor = '#0000%02x'

    tubeMesh.usesSmoothing = True

    # Definition of the underlying points
    tubeMesh.pointList.append([0, 200, 100, 1, 0, 0, 0])
    tubeMesh.pointList.append([70.710678, 200, 70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([100, 200, 0, 1, 0, 0, 0])
    tubeMesh.pointList.append([70.710678, 200, -70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([0, 200, -100, 1, 0, 0, 0])
    tubeMesh.pointList.append([-70.710678, 200, -70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([-100, 200, 0, 1, 0, 0, 0])
    tubeMesh.pointList.append([-70.710678, 200, 70.710678, 1, 0, 0, 0])
    #
    tubeMesh.pointList.append([0, -200, 100, 1, 0, 0, 0])
    tubeMesh.pointList.append([70.710678, -200, 70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([100, -200, 0, 1, 0, 0, 0])
    tubeMesh.pointList.append([70.710678, -200, -70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([0, -200, -100, 1, 0, 0, 0])
    tubeMesh.pointList.append([-70.710678, -200, -70.710678, 1, 0, 0, 0])
    tubeMesh.pointList.append([-100, -200, 0, 1, 0, 0, 0])
    tubeMesh.pointList.append([-70.710678, -200, 70.710678, 1, 0, 0, 0])


    # Definition of the polygons
    # Polys are defined in counter clockwise order when viewed from the outside
    tubeMesh.polyList.append([tubeMesh.pointList[0], tubeMesh.pointList[1], tubeMesh.pointList[9]])
    tubeMesh.polyList.append([tubeMesh.pointList[0], tubeMesh.pointList[9], tubeMesh.pointList[8]])
    tubeMesh.polyList.append([tubeMesh.pointList[1], tubeMesh.pointList[2], tubeMesh.pointList[10]])
    tubeMesh.polyList.append([tubeMesh.pointList[1], tubeMesh.pointList[10], tubeMesh.pointList[9]])
    tubeMesh.polyList.append([tubeMesh.pointList[2], tubeMesh.pointList[3], tubeMesh.pointList[11]])
    tubeMesh.polyList.append([tubeMesh.pointList[2], tubeMesh.pointList[11], tubeMesh.pointList[10]])
    tubeMesh.polyList.append([tubeMesh.pointList[3], tubeMesh.pointList[4], tubeMesh.pointList[12]])
    tubeMesh.polyList.append([tubeMesh.pointList[3], tubeMesh.pointList[12], tubeMesh.pointList[11]])
    #
    tubeMesh.polyList.append([tubeMesh.pointList[4], tubeMesh.pointList[5], tubeMesh.pointList[13]])
    tubeMesh.polyList.append([tubeMesh.pointList[4], tubeMesh.pointList[13], tubeMesh.pointList[12]])
    tubeMesh.polyList.append([tubeMesh.pointList[5], tubeMesh.pointList[6], tubeMesh.pointList[14]])
    tubeMesh.polyList.append([tubeMesh.pointList[5], tubeMesh.pointList[14], tubeMesh.pointList[13]])
    tubeMesh.polyList.append([tubeMesh.pointList[6], tubeMesh.pointList[7], tubeMesh.pointList[15]])
    tubeMesh.polyList.append([tubeMesh.pointList[6], tubeMesh.pointList[15], tubeMesh.pointList[14]])
    tubeMesh.polyList.append([tubeMesh.pointList[7], tubeMesh.pointList[0], tubeMesh.pointList[8]])
    tubeMesh.polyList.append([tubeMesh.pointList[7], tubeMesh.pointList[8], tubeMesh.pointList[15]])

    # Definition of the object
    tubeMesh.meshDef = [tubeMesh.polyList[0], tubeMesh.polyList[1], tubeMesh.polyList[2], tubeMesh.polyList[3],
                        tubeMesh.polyList[4], tubeMesh.polyList[5], tubeMesh.polyList[6], tubeMesh.polyList[7],
                        tubeMesh.polyList[8], tubeMesh.polyList[9], tubeMesh.polyList[10], tubeMesh.polyList[11],
                        tubeMesh.polyList[12], tubeMesh.polyList[13], tubeMesh.polyList[14], tubeMesh.polyList[15]]

    # Definition of the Pyramid's underlying point cloud.  No structure, just the points.
    for i in tubeMesh.pointList:
        tubeMesh.pointCloud.append(i)

    # initialize point cloud copy for resetting
        tubeMesh.initPointCloud()

    # add new mesh to our selected meshes and our list of all meshes
    selectedMeshes = [tubeMesh]
    allMeshes.append(tubeMesh)

    meshNames.append(["tube" + str(numMeshesCreated)])  # add a user-friendly name to be associated with the mesh
    numMeshesCreated += 1  # increment the counter for meshes
    updateMeshList()  # update our UI's mesh list
    tubeMesh.findMidpoint()  # find the midpoint of our new object
    drawScreen()  # draw the screen
    updateTitleBar()
    return tubeMesh

def makeCylinder():
    tube1 = makeTube()
    cap1 = makeCap()
    global selectedMeshes
    global TranslationStepSize, RotationStepSize
    global NIP
    temptranslationstepsize = TranslationStepSize
    TranslationStepSize = 200
    up()
    TranslationStepSize = -200
    cap2 = makeCap()
    up()
    temprotationstepsize = RotationStepSize
    RotationStepSize = 180
    xPlus()
    RotationStepSize = temprotationstepsize
    TranslationStepSize = temptranslationstepsize
    selectedMeshes = [tube1, cap1, cap2]
    tube1.scaleNIP(0.5)
    cap1.scaleNIP(0.5)
    cap2.scaleNIP(0.5)
    tube1.Kd = [0.8314, 0.6863, 0.2157]
    cap1.Kd = [0.8314, 0.6863, 0.2157]
    cap2.Kd = [0.8314, 0.6863, 0.2157]
    drawScreen()

# deletes all selected meshes
def deleteMesh():
    global selectedMeshes
    global allMeshes

    for i in selectedMeshes:  # for each selected mesh
        if i in allMeshes:  # sanity check
            del meshNames[allMeshes.index(i)]  # delete the user-friendly mesh name
            allMeshes.remove(i)  # and delete the associated mesh

    selectedMeshes = []  # empty the list of selected meshes
    updateMeshList()  # update our UI's mesh list
    updateTitleBar()
    drawScreen()  # draw the screen


# updates our UI's list of meshes
def updateMeshList():
    global selectedMeshes
    global allMeshes

    meshList.delete(0, END)  # empty the mesh list

    for i in range(len(allMeshes)):  # for each mesh
        meshList.insert(i, meshNames[i])  # add it to the mesh list

    if len(selectedMeshes) > 0:
        meshList.selection_set(END)


# function called when user changes selection of meshes in the mesh list box
def onSelectionChanged(input):
    global selectedMeshes
    global allMeshes

    selectedMeshes.clear()  # deselect all meshes

    for i in list(meshList.curselection()):  # for each mesh selected in the UI
        selectedMeshes.append(allMeshes[i])  # add it to our selected meshes list

    updateTitleBar()
    drawScreen()  # draw the screen


# multiplies a vector by a 4x4 matrix
def vectorMatrixMult(vector, matrix):
    answerVector = [0, 0, 0, 0]

    # for each column and row we multiply the two values from the two matrices and sum them all up, storing the value in
    # the related index in our new vector
    for col in range(len(matrix)):
        answerVector[col] = 0
        for row in range(len(matrix)):
            answerVector[col] += vector[row] * matrix[row][col]

    return answerVector


# multiplies 2 4x4 matrices
def matrixMult4x4(matrix1, matrix2):
    answerMatrix = [[0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0], [0, 0, 0, 0]]

    # for each column and row and column we multiply the two values from the two matrices and sum them all up, storing
    # the value in the related index in our new matrix
    for i in range(len(matrix1)):
        for j in range(len(matrix2[0])):
            for k in range(len(matrix1[0])):
                answerMatrix[i][j] += matrix1[i][k] * matrix2[k][j]

    return answerMatrix


def clamp(num):
    conversion = 255 / CanvasWidth
    num *= conversion
    if num < 0:
        return 0
    elif num > 255:
        return 255
    else:
        return num


# **************************************************
# ******* Functions for Changing UI Behavior *******


# lower the step size of the "scale" transformation control
def changeScaleStepSizeDown():
    global ScaleStepSize  # access global variable that controls the step size for the transformation controls
    ScaleStepSize -= 0.01  # alter it
    if ScaleStepSize < 0.01:  # confine it
        ScaleStepSize = 0.01
    scalecontrolsstepslabel.config(
        text=str('{:.2f}'.format(round(ScaleStepSize, 2))) + 'x')  # change the text of the label for step size
    if ScaleStepSize < 1:
        scalecontrolslabel2.config(text='(Smaller)')  # if we will be decreasing the size, text changes to indicate this
    if ScaleStepSize == 1:
        scalecontrolslabel2.config(text='(Static)')  # if there will be no change in size, text changes to indicate this


# raise the step size of the "scale" transformation control
def changeScaleStepSizeUp():
    global ScaleStepSize
    ScaleStepSize += 0.01
    if ScaleStepSize > 10:
        ScaleStepSize = 10
    scalecontrolsstepslabel.config(text=str('{:.2f}'.format(round(ScaleStepSize, 2))) + 'x')
    if ScaleStepSize > 1:
        scalecontrolslabel2.config(text='(Larger)')  # if we will be increasing the size, text changes to indicate this
    if ScaleStepSize == 1:
        scalecontrolslabel2.config(text='(Static)')  # if there will be no change in size, text changes to indicate this


# resets the scaling step size to default
def resetScaleStepSize(event):
    global ScaleStepSize
    ScaleStepSize = 1.00
    scalecontrolsstepslabel.config(text=str('{:.2f}'.format(round(ScaleStepSize, 2))) + 'x')
    scalecontrolslabel2.config(text='(Static)')


# lower the step size of the "translation" transformation control
def changeTranslationStepSizeDown():
    global TranslationStepSize
    TranslationStepSize -= 1
    if TranslationStepSize < 1:
        TranslationStepSize = 1
    translationcontrolsstepslabel.config(text=TranslationStepSize)


# raise the step size of the "translation" transformation control
def changeTranslationStepSizeUp():
    global TranslationStepSize
    TranslationStepSize += 1
    if TranslationStepSize > 100:
        TranslationStepSize = 100
    translationcontrolsstepslabel.config(text=TranslationStepSize)


# resets the translation step size to default
def resetTranslationStepSize(event):
    global TranslationStepSize
    TranslationStepSize = 5
    translationcontrolsstepslabel.config(text=str(TranslationStepSize))


# lower the step size of the "rotation" transformation control
def changeRotationStepSizeDown():
    global RotationStepSize
    RotationStepSize -= 1
    if RotationStepSize < 1:
        RotationStepSize = 1
    rotationcontrolsstepslabel.config(text=str(RotationStepSize) + '°')


# raise the step size of the "rotation" transformation control
def changeRotationStepSizeUp():
    global RotationStepSize
    RotationStepSize += 1
    if RotationStepSize > 180:
        RotationStepSize = 180
    rotationcontrolsstepslabel.config(text=str(RotationStepSize) + '°')


# resets the rotation step size to default
def resetRotationStepSize(event):
    global RotationStepSize
    RotationStepSize = 5
    rotationcontrolsstepslabel.config(text=str(RotationStepSize) + '°')


# toggles the usage of world-coordinates vs local-coordinates
def toggleNIP():
    global NIP
    if not NIP:
        NIP = True
    else:
        NIP = False


# Handles screen and viewport resizing and recalculating. Whenever the window size is change by the user, set the new
# width and height of our canvas to the new midpoint, so that the origin stays at the center of the canvas.
def updateCanvasCoords(event):
    global CanvasHeight
    global CanvasWidth
    global zbuffer

    CanvasWidth = event.width
    CanvasHeight = event.height

    zbuffer = [[0 for x in range(CanvasHeight)] for y in range(CanvasWidth)]
    drawScreen()


# update what is written on the title bar with the number of meshes and selected meshes
def updateTitleBar():
    if len(allMeshes) == 1:
        meshesString = 'Mesh'
    else:
        meshesString = 'Meshes'
    root.wm_title("Sweet Engine v0.2 -- " + str(len(allMeshes)) + " "
                  + meshesString + " (" + str(len(selectedMeshes)) + " Selected)")


def togglePolyFill():
    global drawEdges
    global isFilled
    global isWireframe
    global isZbuffered

    if isFilled is False and drawEdges is True:
        isFilled = True
    elif isFilled is True and drawEdges is True:
        drawEdges = False
    elif isFilled is True and drawEdges is False:
        isFilled = False
        drawEdges = True

    drawScreen()


def toggleBackfaceCulling():
    global isWireframe

    if isWireframe == True:
        isWireframe = False
    else:
        isWireframe = True

    drawScreen()


def toggleZbuffer():
    global isZbuffered

    if isZbuffered == True:
        isZbuffered = False
    else:
        isZbuffered = True

    drawScreen()


def toggleLighting():
    global lightingmode

    if lightingmode == 1:
        lightingmode = 2
    elif lightingmode == 2:
        lightingmode = 0
    else:
        lightingmode = 1

    drawScreen()


def toggleShading():
    global shadingmode

    if shadingmode == 1:
        shadingmode = 2
    elif shadingmode == 2:
        shadingmode = 0
    else:
        shadingmode = 1

    drawScreen()


# *****************************************************
# ***************** TKinter layout ********************

root = Tk()
root.minsize(444, 519)
root.geometry("444x519")
root.wm_title("Sweet Engine v0.2")

outerframe = Frame(root)
outerframe.pack(fill="both", expand=True)

selectionpanel = Frame(outerframe, height=400, width=400)
selectionpanel.pack(side=LEFT, fill=Y, expand=0, anchor=W)

lightingbutton = Button(selectionpanel, text="Toggle Lighting", fg="blue", command=toggleLighting)
lightingbutton.pack(fill=X, expand=0)

shadingbutton = Button(selectionpanel, text="Toggle Shading", fg="blue", command=toggleShading)
shadingbutton.pack(fill=X, expand=0)

createpyramidbutton = Button(selectionpanel, text="New Pyramid", fg="green", command=makePyramid)
createpyramidbutton.pack(fill=X, expand=0)

createtubebutton = Button(selectionpanel, text="New Tube", fg="green", command=makeTube)
createtubebutton.pack(fill=X, expand=0)

createcylinderbutton = Button(selectionpanel, text="New Cylinder", fg="green", command=makeCylinder)
createcylinderbutton.pack(fill=X, expand=0)

createcapbutton = Button(selectionpanel, text="New Cap", fg="green", command=makeCap)
createcapbutton.pack(fill=X, expand=0)

createcubebutton = Button(selectionpanel, text="New Cube", fg="green", command=makeCube)
createcubebutton.pack(fill=X, expand=0)

deletemeshbutton = Button(selectionpanel, text="Delete Mesh", fg="red", command=deleteMesh)
deletemeshbutton.pack(fill=X, expand=0)

rightframe = Frame(outerframe)
rightframe.pack(side=RIGHT, fill="both", expand=True)

w = Canvas(rightframe, width=CanvasWidth, height=CanvasHeight, bg="white", relief=RIDGE, borderwidth=4)
w.pack(side=TOP, fill="both", expand=True)
w.bind('<Configure>', updateCanvasCoords)

controlpanel = Frame(rightframe, height=400)
controlpanel.pack(side=BOTTOM)

scrollbar = Scrollbar(selectionpanel, orient="vertical")
meshList = Listbox(selectionpanel, selectmode=EXTENDED, height=30, yscrollcommand=scrollbar.set)
scrollbar.config(command=meshList.yview)
scrollbar.pack(side="right", fill="y")
meshList.bind('<<ListboxSelect>>', onSelectionChanged)
meshList.pack(fill="both", expand=True)

resetcontrols = Frame(controlpanel, height=400, borderwidth=2, relief=RIDGE)
resetcontrols.pack(side=TOP)

coordcheckbox = Checkbutton(resetcontrols, text="Use World-Space Coordinates", command=toggleNIP)
coordcheckbox.pack(side=RIGHT)

resetButton = Button(resetcontrols, text="Reset", fg="red", command=reset)
resetButton.pack(side=LEFT)

togglefillbutton = Button(resetcontrols, text="Toggle Fill", command=togglePolyFill)
togglefillbutton.pack(side=LEFT)

togglecullbutton = Button(resetcontrols, text="Toggle BFC", command=toggleBackfaceCulling)
togglecullbutton.pack(side=LEFT)

togglezbufferbutton = Button(resetcontrols, text="Toggle Z-Buffer", command=toggleZbuffer)
togglezbufferbutton.pack(side=LEFT)

# scale step controls

scalecontrolssteps = Frame(controlpanel, borderwidth=4, relief=RIDGE)
scalecontrolssteps.pack(side=LEFT)

scaleUpButton = Button(scalecontrolssteps, text="▲", command=changeScaleStepSizeUp, repeatdelay=500, repeatinterval=25)
scaleUpButton.pack(side=TOP)

scalecontrolsstepslabel = Label(scalecontrolssteps, text="1.00x")
scalecontrolsstepslabel.bind('<Button-1>', resetScaleStepSize)
scalecontrolsstepslabel.pack()

scaleDownButton = Button(scalecontrolssteps, text="▼", command=changeScaleStepSizeDown, repeatdelay=500,
                         repeatinterval=25)
scaleDownButton.pack(side=BOTTOM)

########

scalecontrols = Frame(controlpanel, borderwidth=4, relief=RIDGE)
scalecontrols.pack(side=LEFT)

scalecontrolslabel = Label(scalecontrols, text="Scale", fg="green")
scalecontrolslabel.pack(side=TOP)

scalecontrolslabel2 = Label(scalecontrols, text="(Static)", fg="green")
scalecontrolslabel2.pack()

scaleButton = Button(scalecontrols, text="Scale", command=scaler, repeatdelay=500, repeatinterval=100)
scaleButton.pack(side=BOTTOM)

# translation step controls

translationcontrolssteps = Frame(controlpanel, borderwidth=4, relief=RIDGE)
translationcontrolssteps.pack(side=LEFT)

translationUpButton = Button(translationcontrolssteps, text="▲", command=changeTranslationStepSizeUp, repeatdelay=500,
                             repeatinterval=50)
translationUpButton.pack(side=TOP)

translationcontrolsstepslabel = Label(translationcontrolssteps, text="5")
translationcontrolsstepslabel.bind('<Button-1>', resetTranslationStepSize)
translationcontrolsstepslabel.pack()

translationDownButton = Button(translationcontrolssteps, text="▼", command=changeTranslationStepSizeDown,
                               repeatdelay=500, repeatinterval=50)
translationDownButton.pack(side=BOTTOM)

########

translatecontrols = Frame(controlpanel, borderwidth=4, relief=RIDGE)
translatecontrols.pack(side=LEFT)

translatecontrolslabel = Label(translatecontrols, text="Translation", fg="green")
translatecontrolslabel.pack()

translatecontrolsupper = Frame(translatecontrols)
translatecontrolsupper.pack()

translatecontrolslower = Frame(translatecontrols)
translatecontrolslower.pack()

#########

backwardButton = Button(translatecontrolsupper, text="⟱", command=backward, repeatdelay=500, repeatinterval=50)
backwardButton.pack(side=LEFT)

upButton = Button(translatecontrolsupper, text="↑", command=up, repeatdelay=500, repeatinterval=50)
upButton.pack(side=LEFT)

forwardButton = Button(translatecontrolsupper, text="⟰", command=forward, repeatdelay=500, repeatinterval=50)
forwardButton.pack(side=LEFT)

leftButton = Button(translatecontrolslower, text="←", command=left, repeatdelay=500, repeatinterval=50)
leftButton.pack(side=LEFT)

upButton = Button(translatecontrolslower, text="↓", command=down, repeatdelay=500, repeatinterval=50)
upButton.pack(side=LEFT)

rightButton = Button(translatecontrolslower, text="→", command=right, repeatdelay=500, repeatinterval=50)
rightButton.pack(side=LEFT)

# rotation step controls

rotationcontrolssteps = Frame(controlpanel, borderwidth=4, relief=RIDGE)
rotationcontrolssteps.pack(side=LEFT)

rotationUpButton = Button(rotationcontrolssteps, text="▲", command=changeRotationStepSizeUp, repeatdelay=500,
                          repeatinterval=50)
rotationUpButton.pack(side=TOP)

rotationcontrolsstepslabel = Label(rotationcontrolssteps, text="5°")
rotationcontrolsstepslabel.bind('<Button-1>', resetRotationStepSize)
rotationcontrolsstepslabel.pack()

rotationDownButton = Button(rotationcontrolssteps, text="▼", command=changeRotationStepSizeDown, repeatdelay=500,
                            repeatinterval=50)
rotationDownButton.pack(side=BOTTOM)

##########

rotationcontrols = Frame(controlpanel, borderwidth=4, relief=RIDGE)
rotationcontrols.pack(side=LEFT)

rotationcontrolslabel = Label(rotationcontrols, text="Rotation", fg="green")
rotationcontrolslabel.pack()

rotationcontrolsx = Frame(rotationcontrols)
rotationcontrolsx.pack(side=LEFT)

rotationcontrolsy = Frame(rotationcontrols)
rotationcontrolsy.pack(side=LEFT)

rotationcontrolsz = Frame(rotationcontrols)
rotationcontrolsz.pack(side=LEFT)

xPlusButton = Button(rotationcontrolsx, text="X+", command=xPlus, repeatdelay=500, repeatinterval=50)
xPlusButton.pack(side=TOP)

xMinusButton = Button(rotationcontrolsx, text="X-", command=xMinus, repeatdelay=500, repeatinterval=50)
xMinusButton.pack(side=BOTTOM)

yPlusButton = Button(rotationcontrolsy, text="Y+", command=yPlus, repeatdelay=500, repeatinterval=50)
yPlusButton.pack(side=TOP)

yMinusButton = Button(rotationcontrolsy, text="Y-", command=yMinus, repeatdelay=500, repeatinterval=50)
yMinusButton.pack(side=BOTTOM)

zPlusButton = Button(rotationcontrolsz, text="Z+", command=zPlus, repeatdelay=500, repeatinterval=50)
zPlusButton.pack(side=TOP)

zMinusButton = Button(rotationcontrolsz, text="Z-", command=zMinus, repeatdelay=500, repeatinterval=50)
zMinusButton.pack(side=BOTTOM)

# **************************************************************************
# ****************** Place Initialization Conditions Here ******************

mesh = makeCap()
mesh.light([1, 1, 1], [1, 1, 1])

# MUST GO AT END OF PROGRAM!!! PLACE NOTHING BELOW THIS!!!!!!!!!!!!
root.mainloop()
