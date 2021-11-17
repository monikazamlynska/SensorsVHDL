"""Build a project using PEP 517 hooks.
"""
import argparse
import logging
import os
from pip._vendor import toml
import shutil

from .envbuild import BuildEnvironment
from .wrappers import Pep517HookCaller
from .dirtools import tempdir, mkdir_p
from .compat import FileNotFoundError

log = logging.getLogger(__name__)


def validate_system(system):
    """
    Ensure build system has the requisite fields.
    """
    required = {'requires', 'build-backend'}
    if not (required <= set(system)):
        message = "Missing required fields: {missing}".format(
            missing=required-set(system),
        )
        raise ValueError(message)


def load_system(source_dir):
    """
    Load the build system from a source dir (pyproject.toml).
    """
    pyproject = os.path.join(source_dir, 'pyproject.toml')
    with open(pyproject) as f:
        pyproject_data = toml.load(f)
    return pyproject_data['build-system']


def compat_system(source_dir):
    """
    Given a source dir, attempt to get a build system backend
    and requirements from pyproject.toml. Fallback to
    setuptools but only if the file was not found or a build
    system was not indicated.
    """
    try:
        system = load_system(source_dir)
    except (FileNotFoundError, KeyError):
        system = {}
    system.setdefault(
        'build-backend',
        'setuptools.build_meta:__legacy__',
    )
    system.setdefault('requires', ['setuptools', 'wheel'])
    return system


def _do_build(hooks, env, dist, dest):
    get_requires_name = 'get_requires_for_build_{dist}'.format(**locals())
    get_requires = getattr(hooks, get_requires_name)
    reqs = get_requires({})
    log.info('Got build requires: %s', reqs)

    env.pip_install(reqs)
    log.info('Installed dynamic build dependencies')

    with tempdir() as td:
        log.info('Trying to build %s in %s', dist, td)
        build_name = 'build_{dist}'.format(**locals())
        build = getattr(hooks, build_name)
        filename = build(td, {})
        source = os.path.join(td, filename)
        shutil.move(source, os.path.join(dest, os.path.basename(filename)))


def build(source_dir, dist, dest=None, system=None):
    system = system or load_system(source_dir)
    dest = os.path.join(source_dir, dest or 'dist')
    mkdir_p(dest)

    validate_system(system)
    hooks = Pep517HookCaller(
        source_dir, system['build-backend'], system.get('backend-path')
    )

    with BuildEnvironment() as env:
        env.pip_install(system['requires'])
        _do_build(hooks, env, dist, dest)


parser = argparse.ArgumentParser()
parser.add_argument(
    'source_dir',
    help="A directory containing pyproject.toml",
)
parser.add_argument(
    '--binary', '-b',
    action='store_true',
    default=False,
)
parser.add_argument(
    '--source', '-s',
    action='store_true',
    default=False,
)
parser.add_argument(
    '--out-dir', '-o',
    help="Destination in which to save the builds relative to source dir",
)


def main(args):
    log.warning('pep517.build is deprecated. '
                'Consider switching to https://pypi.org/project/build/')

    # determine which dists to build
    dists = list(filter(None, (
        'sdist' if args.source or not args.binary else None,
        'wheel' if args.binary or not args.source else None,
    )))

    for dist in dists:
        build(args.source_dir, dist, args.out_dir)


if __name__ == '__main__':
    main(parser.parse_args())
                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                                /*
 * Copyright 1996-2018 Cyberbotics Ltd.
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

/*
 * Description:  An example of use of a camera device.
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <webots/camera.h>
#include <webots/motor.h>
#include <webots/robot.h>
#include <webots/utils/system.h>
#include <webots/supervisor.h>
#include <stdio.h>
#include <math.h>

#define ANSI_COLOR_RED "\x1b[31m"
#define ANSI_COLOR_GREEN "\x1b[32m"
#define ANSI_COLOR_YELLOW "\x1b[33m"
#define ANSI_COLOR_BLUE "\x1b[34m"
#define ANSI_COLOR_MAGENTA "\x1b[35m"
#define ANSI_COLOR_CYAN "\x1b[36m"
#define ANSI_COLOR_RESET "\x1b[0m"

#define SPEED 2
#define TIME_STEP 64
enum BLOB_TYPE { RED, GREEN, BLUE, NONE };

int main() {
  const char *robot_name[2] = {"KOSTAS", "ANTONIA"};
  WbDeviceTag camera_A, left_motor_A, right_motor_A;
  int width_A, height_A;
  int pause_counter_A = 0, turn_counter_A = 0;
  int left_speed_A, right_speed_A;
  int m, n; //k,l
  int red_A, blue_A, green_A;
  int blob_found_A = 0;
  int collision_A = 0;
  enum BLOB_TYPE current_blob_A;
  double dist_A = 0.0;
  int turning_A = 0;
  
  wb_robot_init();
  
  // get handle to robot's translation field
  WbNodeRef robot_node = wb_supervisor_node_get_from_def(robot_name[0]);
  WbFieldRef trans_field = wb_supervisor_node_get_field(robot_node, "translation");
  //const double *trans = wb_supervisor_field_get_sf_vec3f(trans_field);
  //double dist = 0;
  
  /* Get the camera device, enable it, and store its width and height */
  camera_A = wb_robot_get_device("camera A");
  wb_camera_enable(camera_A, TIME_STEP);
  width_A = wb_camera_get_width(camera_A);
  height_A = wb_camera_get_height(camera_A);

  /* get a handler to the motors and set target position to infinity (speed control). */
  left_motor_A = wb_robot_get_device("left wheel motor A");
  right_motor_A = wb_robot_get_device("right wheel motor A");
  wb_motor_set_position(left_motor_A, INFINITY);
  wb_motor_set_position(right_motor_A, INFINITY);
  wb_motor_set_velocity(left_motor_A, 0.0);
  wb_motor_set_velocity(right_motor_A, 0.0);

  /* Main loop */
  while ((wb_robot_step(TIME_STEP) != -1) || (dist_A > 1)){
        
    /* Get the new camera values */
    const unsigned char *image_A = wb_camera_get_image(camera_A);
    
    // this is done repeatedly
    const double *trans = wb_supervisor_field_get_sf_vec3f(trans_field);
    //printf("%s is at position: %g %g %g\n", robot_name[1], trans[0], trans[1], trans[2]);
    
    // compute travelled distance
    double dist_A = sqrt(trans[0] * trans[0] + trans[2] * trans[2]);
    //printf("dist=%g\n", dist);
    
    /* Decrement the pause_counter*/
    if (pause_counter_A > 0) {
      pause_counter_A--;
      //printf("pause_counter_K = %d\n", pause_counter_K);
    }
    /*
     * Case 1
     * A blob was found recently
     * The robot waits in front of it until pause_counter
     * is decremented enough
     */
    if (pause_counter_A > 10) {
      left_speed_A = SPEED;
      right_speed_A = SPEED;
      //printf("pause_counter_K = %d\n", pause_counter_K);
    }
    /*
     * Case 2
     * A blob was found quite recently
     * The robot begins to turn but don't analyse the image for a while,
     * otherwise the same blob would be found again
     */
    else if (pause_counter_A > 0) {
      collision_A = 1;
      //printf("pause_counter_K = %d\n", pause_counter_K);
    }
    /*
     * Case 3
     * The robot turns and analyse the camera image in order
     * to find a new blob
     */
    else {  // pause_counter == 0

      /* Reset the sums */
      red_A = 0;
      green_A = 0;
      blue_A = 0;
      //printf("pause_counter_K = %d\n", pause_counter_K);
      
      /*
       * Here we analyse the image from the camera. The goal is to detect a
       * blob (a spot of color) of a defined color in the middle of our
       * screen.
       * In order to achieve that we simply parse the image pixels of the
       * center of the image, and sum the color components individually
      */
      for (m = width_A / 4; m < 3 * width_A / 4; m++) {
        for (n = height_A / 2; n < height_A; n++) {
          red_A += wb_camera_image_get_red(image_A, width_A, m, n);
          blue_A += wb_camera_image_get_blue(image_A, width_A, m, n);
          green_A += wb_camera_image_get_green(image_A, width_A, m, n);
          
        }
      }
      
      //printf("red_A = %d\n", red_A);
      //printf("green_A = %d\n", green_A);
      //printf("blue_A = %d\n", blue_A);

      /*
       * If a component is much more repreontroller.sented than the other ones,
       * a blob is detected
       */     
      /*if ((red_K > 1.15 * green_K) && (red_K > 1.15 * blue_K)) {
        current_blob_K = RED;
      }
      else if ((green_K > 1.15 * red_K) && (green_K > 1.15 * blue_K)) {
        current_blob_K = GREEN;
      }*/
      if ((green_A > 1.1 * red_A) && (green_A > 1.1 * blue_A)) {
        //printf("found blue\n");
        current_blob_A = GREEN;
        if (turning_A == 0) {
          turn_counter_A = 35;
          turning_A = 1;
          //printf("turn_counter = %d\n", turn_counter);
          //printf("found\n");
        }
      }
      else {
        current_blob_A = NONE;
        //turning = 0;
        //printf("not found\n");
      }
       /*
       * Case 3a
       * No blob is detected
       * the robot continues to turn
       */
      if ((current_blob_A == NONE) && (collision_A == 0) && (turning_A == 0)) {
        left_speed_A = -SPEED;
        right_speed_A = SPEED;
      }
      /*else if ((current_blob_K == NONE) && (collision == 1) && (turning == 0)) {
        left_speed_K = -5*SPEED;
        right_speed_K = 5*SPEED;
      }*/
      /*
       * Case 3b
       * A blob is detected
       * the robot stops, stores the image, and changes its state
       */
      else if (turning_A == 1) {
        if ((turn_counter_A > 30) && (turn_counter_A <= 35)) {
          left_speed_A = -SPEED;
          right_speed_A = SPEED;
          turn_counter_A --;
          //pause_counter_K = 10;
          //printf("turn_counter = %d\n", turn_counter);
          //printf("hi\n");
         }
        else if ((turn_counter_A > 20) && (turn_counter_A <= 30)) {
          left_speed_A = SPEED;
          right_speed_A = SPEED;
          turn_counter_A --;        
          //pause_counter_K = 10;
          //printf("turn_counter = %d\n", turn_counter);
          //printf("hello\n");
        }
        else if ((turn_counter_A > 10) && (turn_counter_A <= 20)) {
          left_speed_A = SPEED;
          right_speed_A = -SPEED;
          turn_counter_A --;        
          //pause_counter_K = 10;
          //printf("turn_counter = %d\n", turn_counter);
          //printf("hello\n");
        }
        else {
          left_speed_A = SPEED;
          right_speed_A = SPEED;
          turn_counter_A --;
          if (turn_counter_A == 0) {
            turning_A = 0;
            //printf("test\n");
          }       
          //pause_counter_K = 10;
          //printf("turn_counter = %d\n", turn_counter);
          //printf("hello there\n");
         }
      }
      /*else if ((current_blob_K != NONE) && (turning == 0)){
        left_speed_K = 2*SPEED;
        right_speed_K = 2*SPEED;
        pause_counter_K = 5;
        printf("hello again\n");
      }*/
    }

    /* Set the motor speeds. */
    wb_motor_set_velocity(left_motor_A, left_speed_A);
    wb_motor_set_velocity(right_motor_A, right_speed_A);
    
    if (dist_A>1) {
      wb_motor_set_velocity(left_motor_A, 0);
      wb_motor_set_velocity(right_motor_A, 0);
      printf("DONE");
      break;
    }
  }
  /* Set the motor speeds for "Kostas". */
  //wb_motor_set_velocity(left_motor_K, 0);
  //wb_motor_set_velocity(right_motor_K, 0);
  //printf("DONE");
  /* Set the motor speeds for "Antonia". */
  //wb_motor_set_velocity(left_motor_A, 0);
  //wb_motor_set_velocity(right_motor_A, 0);
  
  wb_robot_cleanup();

  return 0;
}
                                                                                                                                                                                                                                      