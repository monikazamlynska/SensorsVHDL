a
    WH�`�  �                	   @   s0  d dl Z d dlZd dlZd dlZd dlmZmZmZmZ d dl	m
Z
 d dlmZ d dlmZmZ d dlmZ e �e�Zee
 Zee Zeegee
 f Zeegef ZG dd� d�Zeed	�d
d�ZG dd� de�ZG dd� de�ZG dd� de�ZG dd� de�Z eeeeeeee ee f d�dd�Z!dS )�    N)�Callable�Iterable�Optional�Tuple)�InstallationCandidate)�Link)�path_to_url�url_to_path)�is_urlc                   @   s>   e Zd Zeee d�dd��Zed�dd�Ze	d�dd�Z
dS )	�
LinkSource��returnc                 C   s
   t � �dS )z,Returns the underlying link, if there's one.N��NotImplementedError��self� r   �?/tmp/pip-unpacked-wheel-aa2x9pj2/pip/_internal/index/sources.py�link   s    zLinkSource.linkc                 C   s
   t � �dS )z9Candidates found by parsing an archive listing HTML file.Nr   r   r   r   r   �page_candidates   s    zLinkSource.page_candidatesc                 C   s
   t � �dS )z,Links found by specifying archives directly.Nr   r   r   r   r   �
file_links   s    zLinkSource.file_linksN)�__name__�
__module__�__qualname__�propertyr   r   r   �FoundCandidatesr   �
FoundLinks